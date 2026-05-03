import pytest
import sys
import os

# Ensure the parent directory is in the path to import proof_core
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import proof_core as core

class TestParser:
    """
    Test the parsing logic.
    Note: The lexer defines variables as starting with lowercase [a-z] 
    and constants/predicates as starting with uppercase [A-Z].
    """
    
    @pytest.mark.parametrize("input_str, expected", [
        # Uppercase 'A' and 'B' are parsed as predicates ('pred')
        ("A -> B", ('implies', ('pred', 'A', []), ('pred', 'B', []))),
        ("A and B", ('and', ('pred', 'A', []), ('pred', 'B', []))),
        ("A or B", ('or', ('pred', 'A', []), ('pred', 'B', []))),
        # Lowercase 'a' and 'b' are parsed as variables ('var')
        ("a -> b", ('implies', ('var', 'a'), ('var', 'b'))),
        # Quantifiers
        ("forall x. P(x)", ('forall', 'x', ('pred', 'P', [('var', 'x')]))),
    ])
    def test_parser_cases(self, input_str, expected):
        """Test various parsing scenarios using parametrization."""
        prop = core.parse_formula(input_str)
        assert prop == expected

class TestTactics:
    """Test individual tactic behaviors."""
    
    def test_intro_implication(self):
        # Goal: A -> B
        state = core.ProofState([([], ('implies', ('pred', 'A', []), ('pred', 'B', [])))])
        new_state = core.tactic_intro(state, "H")
        
        assert len(new_state.goals) == 1
        ctx, goal = new_state.goals[0]
        assert goal == ('pred', 'B', [])
        assert ("H", ('pred', 'A', [])) in ctx

    def test_intro_forall(self):
        # Goal: forall x, P(x)
        state = core.ProofState([([], ('forall', 'x', ('pred', 'P', [('var', 'x')])))])
        new_state = core.tactic_intro(state, "y")
        
        # The goal should now be P(y)
        ctx, goal = new_state.goals[0]
        assert goal == ('pred', 'P', [('var', 'y')])

    def test_exact(self):
        # Goal: A, Context: H: A
        state = core.ProofState([([("H", ('pred', 'A', []))], ('pred', 'A', []))])
        new_state = core.tactic_exact(state, "H")
        assert new_state.is_complete()

    def test_split(self):
        # Goal: A and B
        state = core.ProofState([([], ('and', ('pred', 'A', []), ('pred', 'B', [])))])
        new_state = core.tactic_split(state)
        
        assert len(new_state.goals) == 2
        assert new_state.goals[0][1] == ('pred', 'A', [])
        assert new_state.goals[1][1] == ('pred', 'B', [])

    def test_left_right(self):
        # Goal: A or B
        state = core.ProofState([([], ('or', ('pred', 'A', []), ('pred', 'B', [])))])
        
        state_left = core.tactic_left(state)
        assert state_left.goals[0][1] == ('pred', 'A', [])
        
        state_right = core.tactic_right(state)
        assert state_right.goals[0][1] == ('pred', 'B', [])

class TestProofFlow:
    """Test full proof workflows and state management."""
    
    def test_simple_proof(self):
        # Prove A -> A
        state = None
        state, msg = core.process_command(state, "goal A -> A")
        assert state is not None
        
        state, msg = core.process_command(state, "intro H")
        assert len(state.goals) == 1
        
        state, msg = core.process_command(state, "exact H")
        assert state.is_complete()
        
    def test_undo_redo(self):
        state = None
        state, _ = core.process_command(state, "goal A -> A")
        state, _ = core.process_command(state, "intro H")
        
        # Undo
        state, msg = core.process_command(state, "undo")
        assert "Undone" in msg
        assert len(state.goals) == 1
        # Context should be empty after undoing the intro
        assert state.goals[0][0] == [] 
        
        # Redo
        state, msg = core.process_command(state, "redo")
        assert "Redone" in msg
        # Context should have H again
        assert state.goals[0][0][0][0] == "H"

    def test_assumption(self):
        # Prove A -> A using assumption tactic
        state, _ = core.process_command(None, "goal A -> A")
        state, _ = core.process_command(state, "intro H")
        state, msg = core.process_command(state, "assumption")
        assert state.is_complete()