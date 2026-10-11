import os
import sys
import pytest
import tempfile
import shutil
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add the project directory to Python path
sys.path.insert(0, str(Path(__file__).parent.parent))

from proof_assistant import (
    parse_formula, parse_term, prop_repr, term_repr,
    ProofState, ProofTree, Context, Prop, Term,
    tactic_intro, tactic_exact, tactic_split, tactic_assumption,
    tactic_forall_elim, tactic_exists_intro, tactic_reflexivity,
    tactic_contradiction, tactic_left, tactic_right,
    tactic_not_intro, tactic_dne
)

class TestProofAssistantCore:
    """Test core functionality and parsing"""
    
    def test_parsing_simple_propositions(self):
        """Test parsing basic propositions"""
        assert prop_repr(parse_formula("P")) == "P"
        assert prop_repr(parse_formula("P → Q")) == "P → Q"
        assert prop_repr(parse_formula("P ∧ Q")) == "P ∧ Q"
        assert prop_repr(parse_formula("P ∨ Q")) == "P ∨ Q"
        assert prop_repr(parse_formula("¬P")) == "¬P"
    
    def test_parsing_quantifiers(self):
        """Test parsing quantified formulas"""
        assert prop_repr(parse_formula("∀x. P(x)")) == "∀x. P(x)"
        assert prop_repr(parse_formula("∃x. P(x)")) == "∃x. P(x)"
        assert prop_repr(parse_formula("∀x. P(x) → Q(x)")) == "∀x. P(x) → Q(x)"
    
    def test_parsing_equality(self):
        """Test parsing equality expressions"""
        assert prop_repr(parse_formula("x = y")) == "x = y"
        assert prop_repr(parse_formula("f(x) = g(y)")) == "f(x) = g(y)"
    
    def test_term_parsing(self):
        """Test parsing terms"""
        assert term_repr(parse_term("x")) == "x"
        assert term_repr(parse_term("f(x,y)")) == "f(x, y)"
        assert term_repr(parse_term("c")) == "c"

class TestSimpleProofs:
    """Test simple proof constructions"""
    
    def test_propositional_implication(self):
        """Test proving a simple implication"""
        # Goal: P → P
        goal = parse_formula("P → P")
        state = ProofState([([], goal)])
        
        # Apply intro tactic
        state = tactic_intro(state, "H")
        
        # Apply exact tactic with hypothesis H
        state = tactic_exact(state, "H")
        
        assert state.is_complete(), "Proof should be complete"
        assert len(state.proof_tree.steps) == 2, "Should have 2 proof steps"
    
    def test_conjunction_proof(self):
        """Test proving a conjunction"""
        # Goal: P → Q → P ∧ Q
        goal = parse_formula("P → Q → P ∧ Q")
        state = ProofState([([], goal)])
        
        # Apply intro tactics twice
        state = tactic_intro(state, "Hp")
        state = tactic_intro(state, "Hq")
        
        # Apply split to create two subgoals
        state = tactic_split(state)
        
        # Prove first goal (P) using Hp
        state = tactic_exact(state, "Hp")
        
        # Prove second goal (Q) using Hq
        state = tactic_exact(state, "Hq")
        
        assert state.is_complete(), "Proof should be complete"
        assert len(state.proof_tree.steps) == 5, "Should have 5 proof steps"

class TestAdvancedProofs:
    """Test more complex proof scenarios"""
    
    def test_forall_elimination(self):
        """Test universal quantifier elimination"""
        # Goal: (∀x. P(x)) → P(a)
        goal = parse_formula("(∀x. P(x)) → P(a)")
        state = ProofState([([], goal)])
        
        # Introduce hypothesis
        state = tactic_intro(state, "Hforall")
        
        # Eliminate universal quantifier with term 'a'
        a_term = parse_term("a")
        current_ctx, _ = state.current()
        hyp_idx = 0  # Index of universal hypothesis
        
        state = tactic_forall_elim(state, hyp_idx, a_term)
        
        # Use assumption to complete proof
        state = tactic_assumption(state)
        
        assert state.is_complete(), "Proof should be complete"
    
    def test_exists_introduction(self):
        """Test existential quantifier introduction"""
        # Goal: P(a) → ∃x. P(x)
        goal = parse_formula("P(a) → ∃x. P(x)")
        state = ProofState([([], goal)])
        
        # Introduce hypothesis
        state = tactic_intro(state, "Hpa")
        
        # Provide witness 'a' for existential
        a_term = parse_term("a")
        state = tactic_exists_intro(state, a_term)
        
        # Complete with assumption
        state = tactic_assumption(state)
        
        assert state.is_complete(), "Proof should be complete"

def run_proof_script(script_path: str) -> bool:
    """Run a proof script and return whether it completed successfully"""
    state = None
    
    with open(script_path, 'r') as f:
        for line in f:
            cmd = line.strip()
            if not cmd or cmd.startswith('#'):
                continue
                
            # Process command and update state
            state = process_command_for_testing(state, cmd)
            
            # Check for errors in state
            if hasattr(state, 'error') and state.error:
                print(f"Error in script {script_path}: {state.error}")
                return False
    
    return state is not None and state.is_complete()

def process_command_for_testing(state, command):
    """Simplified command processor for testing"""
    # Implementation simplified for testing purposes
    # This would mirror the functionality of process_command in the main code
    return state

class TestProofScripts:
    """Test running proof scripts from files"""
    
    @pytest.fixture(autouse=True)
    def setup_test_dir(self, tmp_path):
        """Setup test directory structure with proof scripts"""
        # Create ProofScripts directory
        proof_dir = tmp_path / "ProofScripts"
        proof_dir.mkdir()
        
        # Create test proof scripts
        scripts = {
            "basic_propositional.proof": """
                goal P → P
                intro H
                exact H
            """,
            "conjunction.proof": """
                goal P → Q → P ∧ Q
                intro Hp
                intro Hq
                split
                exact Hp
                exact Hq
            """,
            "quantifiers.proof": """
                goal (∀x. P(x)) → P(a)
                intro H
                forall_elim 0 a
                assumption
            """,
            "exists.proof": """
                goal P(a) → ∃x. P(x)
                intro H
                exists_intro a
                assumption
            """,
            "equality.proof": """
                goal ∀x. x = x
                intro x
                reflexivity
            """,
            "complex_proof.proof": """
                goal (P → Q) → (Q → R) → P → R
                intro Hpq
                intro Hqr
                intro Hp
                exact Hqr
                exact Hpq
                exact Hp
            """,
            "double_negation.proof": """
                goal ¬¬P → P
                intro Hnnp
                dne Hnnp
            """
        }
        
        # Write scripts to files
        for filename, content in scripts.items():
            with open(proof_dir / filename, 'w') as f:
                f.write(content.strip())
        
        self.proof_dir = proof_dir
        yield
    
    def test_run_all_proof_scripts(self):
        """Test all proof scripts in the ProofScripts folder"""
        success_count = 0
        total_count = 0
        
        for script_file in self.proof_dir.glob("*.proof"):
            total_count += 1
            print(f"\nRunning test: {script_file.name}")
            
            try:
                completed = run_proof_script(str(script_file))
                if completed:
                    success_count += 1
                    print(f"✓ {script_file.name} completed successfully")
                else:
                    print(f"✗ {script_file.name} failed to complete")
            except Exception as e:
                print(f"✗ {script_file.name} crashed: {str(e)}")
        
        print(f"\nTest summary: {success_count}/{total_count} proofs completed")
        assert success_count > 0, "No proofs completed successfully"
        assert success_count == total_count, f"{total_count - success_count} proofs failed"
    
    def test_export_functionality(self):
        """Test Coq export functionality"""
        # Create a simple proof
        goal = parse_formula("P → P")
        state = ProofState([([], goal)])
        state = tactic_intro(state, "H")
        state = tactic_exact(state, "H")
        
        # Export to Coq
        coq_code = state.proof_tree.export_coq("refl_implication")
        
        # Verify export contains expected elements
        assert "Theorem refl_implication" in coq_code
        assert "intros H." in coq_code
        assert "exact H." in coq_code
        assert "Qed." in coq_code
        
        print("Coq export test passed:")
        print(coq_code)

def test_error_handling():
    """Test error handling for invalid commands and proofs"""
    # Test invalid tactic application
    goal = parse_formula("P ∧ Q")
    state = ProofState([([], goal)])
    
    # Should fail: trying to use intro on conjunction
    try:
        state = tactic_intro(state, "H")
        assert False, "Should have raised an exception for invalid tactic"
    except Exception as e:
        assert "not implication or forall" in str(e).lower()
    
    # Test invalid exact tactic
    goal = parse_formula("P")
    state = ProofState([([], goal)])
    
    try:
        state = tactic_exact(state, "nonexistent")
        assert False, "Should have raised an exception for invalid hypothesis"
    except Exception as e:
        assert "doesn't match goal" in str(e).lower()

if __name__ == "__main__":
    pytest.main([__file__, "-v"])