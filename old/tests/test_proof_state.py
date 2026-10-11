import pytest
import json
import os
from proof_assistant import (
    ProofState, ProofTree, parse_formula, tactic_intro, tactic_exact,
    tactic_split, tactic_assumption, tactic_forall_elim
)

def test_state_serialization(simple_implication_state, temp_dir):
    """Test saving and loading proof state"""
    state = simple_implication_state
    
    # Complete the proof
    state = tactic_intro(state, "H")
    state = tactic_exact(state, "H")
    
    # Save proof state
    filename = os.path.join(temp_dir, "test_proof.json")
    state.proof_tree.save_proof_state(filename)
    
    # Verify file exists and contains valid JSON
    assert os.path.exists(filename)
    with open(filename, 'r') as f:
        data = json.load(f)
        assert "theorem_name" in data
        assert "initial_goal" in data
        assert "steps" in data
        assert len(data["steps"]) == 2
    
    # Load proof state
    new_tree = ProofTree()
    new_tree.load_proof_state(filename)
    
    # Verify loaded state
    assert new_tree.theorem_name == "reflexive_implication"
    assert len(new_tree.steps) == 2
    assert new_tree.steps[0].tactic_name == "tactic_intro"
    assert new_tree.steps[1].tactic_name == "tactic_exact"

def test_incomplete_proof_serialization(conjunction_state, temp_dir):
    """Test saving/loading incomplete proof"""
    state = conjunction_state
    
    # Do partial proof
    state = tactic_intro(state, "Hp")
    state = tactic_intro(state, "Hq")
    state = tactic_split(state)
    state = tactic_exact(state, "Hp")
    # Leave second goal unproven
    
    # Save proof state
    filename = os.path.join(temp_dir, "incomplete_proof.json")
    state.proof_tree.save_proof_state(filename)
    
    # Load proof state
    new_tree = ProofTree()
    new_tree.load_proof_state(filename)
    
    # Verify loaded state has correct number of steps
    assert len(new_tree.steps) == 4
    assert not new_tree.steps[-1].success  # Last step might be incomplete

def test_state_history_management(simple_implication_state):
    """Test state history management"""
    state = simple_implication_state
    
    # Initial state
    assert len(state.history) == 0
    assert len(state.future) == 0
    
    # Apply intro tactic
    next_state = tactic_intro(state, "H")
    assert len(next_state.history) == 1
    assert len(next_state.future) == 0
    assert next_state.history[0][1] != next_state.proof_tree.steps  # History has old steps
    
    # Apply exact tactic
    final_state = tactic_exact(next_state, "H")
    assert len(final_state.history) == 2
    assert len(final_state.future) == 0
    
    # Undo last step
    undone_state = final_state.undo()
    assert len(undone_state.history) == 1
    assert len(undone_state.future) == 1
    assert not undone_state.is_complete()
    
    # Redo the step
    redone_state = undone_state.redo()
    assert len(redone_state.history) == 2
    assert len(redone_state.future) == 0
    assert redone_state.is_complete()

def test_error_recording(simple_implication_state):
    """Test error recording in proof steps"""
    state = simple_implication_state
    
    # Initial state
    assert len(state.proof_tree.steps) == 0
    
    # Apply intro tactic (should succeed)
    state = tactic_intro(state, "H")
    assert len(state.proof_tree.steps) == 1
    assert state.proof_tree.steps[0].success == True
    
    # Try to apply intro again on P (should fail)
    try:
        state = tactic_intro(state, "H2")
        pytest.fail("Should have raised an exception")
    except Exception as e:
        # Verify error was recorded
        assert len(state.proof_tree.steps) == 2
        assert state.proof_tree.steps[1].success == False
        assert state.proof_tree.steps[1].error_message is not None
        assert "not implication or forall" in state.proof_tree.steps[1].error_message.lower()

def test_state_with_context(simple_implication_state):
    """Test state preservation with context"""
    state = simple_implication_state
    
    # Apply intro tactic
    state = tactic_intro(state, "H")
    
    # Get current context and goal
    ctx, goal = state.current()
    assert len(ctx) == 1
    assert ctx[0][0] == "H"
    assert prop_repr(ctx[0][1]) == "P"
    assert prop_repr(goal) == "P"
    
    # Verify context display
    state_str = str(state)
    assert "H : P" in state_str
    assert "Goal: P" in state_str