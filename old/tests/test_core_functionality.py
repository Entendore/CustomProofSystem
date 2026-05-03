import pytest
from proof_assistant import (
    ProofState, ProofTree, prop_repr, term_repr, alpha_eq,
    substitute, free_vars, free_vars_term, beta_reduce
)

def test_proof_state_initialization(empty_proof_state):
    """Test basic proof state initialization"""
    state = empty_proof_state
    assert len(state.goals) == 0
    assert state.is_complete()
    assert len(state.proof_tree.steps) == 0
    assert state.current() is None

def test_proof_tree_recording(simple_implication_state):
    """Test that proof steps are properly recorded"""
    state = simple_implication_state
    
    # Initial state
    assert len(state.proof_tree.steps) == 0
    assert not state.is_complete()
    
    # Apply intro tactic
    state = tactic_intro(state, "H")
    assert len(state.proof_tree.steps) == 1
    assert state.proof_tree.steps[0].tactic_name == "tactic_intro"
    assert state.proof_tree.steps[0].success == True
    
    # Apply exact tactic
    state = tactic_exact(state, "H")
    assert len(state.proof_tree.steps) == 2
    assert state.proof_tree.steps[1].tactic_name == "tactic_exact"
    assert state.proof_tree.steps[1].success == True
    assert state.is_complete()

def test_proof_display(simple_implication_state):
    """Test proof state display formatting"""
    state = simple_implication_state
    state_str = str(state)
    
    assert "Proof state: 1 remaining goal(s)" in state_str
    assert "Goal: P → P" in state_str
    assert ">>> Goal 1:" in state_str
    assert "Context: ∅" in state_str

def test_alpha_equivalence():
    """Test alpha equivalence of formulas"""
    from proof_assistant import parse_formula, alpha_eq
    
    # Same formula
    f1 = parse_formula("P → Q")
    f2 = parse_formula("P → Q")
    assert alpha_eq(f1, f2)
    
    # Alpha equivalent formulas with bound variables
    f3 = parse_formula("∀x. P(x)")
    f4 = parse_formula("∀y. P(y)")
    assert alpha_eq(f3, f4)
    
    # Not alpha equivalent
    f5 = parse_formula("∀x. P(x)")
    f6 = parse_formula("∀x. Q(x)")
    assert not alpha_eq(f5, f6)
    
    # More complex alpha equivalence
    f7 = parse_formula("∀x. ∃y. P(x, y)")
    f8 = parse_formula("∀a. ∃b. P(a, b)")
    assert alpha_eq(f7, f8)

def test_substitution():
    """Test substitution in formulas"""
    from proof_assistant import parse_term, substitute
    
    # Simple substitution
    prop = parse_formula("P(x)")
    x_term = parse_term("x")
    a_term = parse_term("a")
    result = substitute(prop, "x", a_term)
    assert prop_repr(result) == "P(a)"
    
    # Substitution in quantified formula
    prop = parse_formula("∀y. P(x, y)")
    result = substitute(prop, "x", a_term)
    assert prop_repr(result) == "∀y. P(a, y)"

def test_free_variables():
    """Test free variable calculation"""
    from proof_assistant import parse_formula, free_vars
    
    # Variables
    assert free_vars(parse_formula("P")) == set()
    assert free_vars(parse_formula("P(x)")) == {"x"}
    
    # Connectives
    f = parse_formula("P(x) ∧ Q(y)")
    assert free_vars(f) == {"x", "y"}
    
    # Quantifiers
    f = parse_formula("∀x. P(x, y)")
    assert free_vars(f) == {"y"}
    
    f = parse_formula("∃z. P(x, z) → Q(y)")
    assert free_vars(f) == {"x", "y"}

def test_undo_redo_functionality(simple_implication_state):
    """Test undo/redo functionality"""
    state = simple_implication_state
    
    # Initial state
    assert len(state.goals) == 1
    assert not state.is_complete()
    
    # Apply intro tactic
    state = tactic_intro(state, "H")
    assert len(state.goals) == 1
    assert not state.is_complete()
    assert len(state.history) == 1
    assert len(state.future) == 0
    
    # Apply exact tactic
    state = tactic_exact(state, "H")
    assert state.is_complete()
    assert len(state.history) == 2
    assert len(state.future) == 0
    
    # Undo last step
    state = state.undo()
    assert not state.is_complete()
    assert len(state.goals) == 1
    assert len(state.history) == 1
    assert len(state.future) == 1
    
    # Undo again
    state = state.undo()
    assert not state.is_complete()
    assert len(state.goals) == 1
    assert len(state.history) == 0
    assert len(state.future) == 2
    
    # Redo
    state = state.redo()
    assert not state.is_complete()
    assert len(state.goals) == 1
    assert len(state.history) == 1
    assert len(state.future) == 1
    
    # Redo again
    state = state.redo()
    assert state.is_complete()
    assert len(state.history) == 2
    assert len(state.future) == 0