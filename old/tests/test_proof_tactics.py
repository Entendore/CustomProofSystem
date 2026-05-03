import pytest
from proof_assistant import (
    tactic_intro, tactic_exact, tactic_split, tactic_assumption,
    tactic_forall_elim, tactic_exists_intro, tactic_reflexivity,
    tactic_contradiction, tactic_left, tactic_right,
    tactic_not_intro, tactic_dne, tactic_auto, tactic_destruct
)

def test_implication_intro_elim(simple_implication_state):
    """Test implication introduction and elimination"""
    state = simple_implication_state
    
    # Apply intro tactic
    state = tactic_intro(state, "H")
    assert len(state.goals) == 1
    ctx, goal = state.current()
    assert len(ctx) == 1
    assert prop_repr(ctx[0][1]) == "P"
    assert prop_repr(goal) == "P"
    
    # Apply exact tactic
    state = tactic_exact(state, "H")
    assert state.is_complete()

def test_conjunction_introduction(conjunction_state):
    """Test conjunction introduction"""
    state = conjunction_state
    
    # Apply intro tactics twice
    state = tactic_intro(state, "Hp")
    state = tactic_intro(state, "Hq")
    
    # Apply split to create two subgoals
    state = tactic_split(state)
    assert len(state.goals) == 2
    
    # Prove first goal (P) using Hp
    state = tactic_exact(state, "Hp")
    assert len(state.goals) == 1
    
    # Prove second goal (Q) using Hq
    state = tactic_exact(state, "Hq")
    assert state.is_complete()

def test_universal_quantifier_elimination(quantifier_state):
    """Test universal quantifier elimination"""
    state = quantifier_state
    
    # Introduce hypothesis
    state = tactic_intro(state, "Hforall")
    
    # Get the hypothesis index
    ctx, _ = state.current()
    hyp_idx = next(i for i, (name, _) in enumerate(ctx) if name == "Hforall")
    
    # Eliminate universal quantifier with term 'a'
    a_term = parse_term("a")
    state = tactic_forall_elim(state, hyp_idx, a_term)
    
    # Use assumption to complete proof
    state = tactic_assumption(state)
    
    assert state.is_complete()

def test_existential_quantifier_introduction(exists_state):
    """Test existential quantifier introduction"""
    state = exists_state
    
    # Introduce hypothesis
    state = tactic_intro(state, "Hpa")
    
    # Provide witness 'a' for existential
    a_term = parse_term("a")
    state = tactic_exists_intro(state, a_term)
    
    # Complete with assumption
    state = tactic_assumption(state)
    
    assert state.is_complete()

def test_equality_reflexivity(equality_state):
    """Test equality reflexivity"""
    state = equality_state
    
    # Introduce variable
    state = tactic_intro(state, "x")
    
    # Apply reflexivity
    state = tactic_reflexivity(state)
    
    assert state.is_complete()

def test_transitivity(complex_state):
    """Test transitivity proof"""
    state = complex_state
    
    # Apply intro tactics
    state = tactic_intro(state, "H1")  # P → Q
    state = tactic_intro(state, "H2")  # Q → R
    state = tactic_intro(state, "H3")  # P
    
    # Compose implications
    state = tactic_exact(state, "H2")  # Need to prove Q
    state = tactic_exact(state, "H1")  # Need to prove P
    state = tactic_exact(state, "H3")  # Prove P
    
    assert state.is_complete()

def test_double_negation_elimination(negation_state):
    """Test double negation elimination"""
    state = negation_state
    
    # Introduce hypothesis
    state = tactic_intro(state, "Hnnp")
    
    # Apply double negation elimination
    state = tactic_dne(state, "Hnnp")
    
    assert state.is_complete()

def test_disjunction_introduction(disjunction_state):
    """Test disjunction introduction"""
    state = disjunction_state
    
    # Introduce hypothesis
    state = tactic_intro(state, "H")
    
    # Prove left disjunct
    state = tactic_left(state)
    state = tactic_exact(state, "H")
    
    assert state.is_complete()

def test_contradiction_principle(contradiction_state):
    """Test contradiction/ex falso principle"""
    state = contradiction_state
    
    # Introduce false hypothesis
    state = tactic_intro(state, "Hfalse")
    
    # Apply contradiction to prove anything
    state = tactic_contradiction(state)
    
    assert state.is_complete()

def test_destruct_and_elimination():
    """Test destruct tactic on conjunction"""
    # Goal: (P ∧ Q) → P
    goal = parse_formula("(P ∧ Q) → P")
    state = ProofState([([], goal)])
    
    # Introduce hypothesis
    state = tactic_intro(state, "Hconj")
    
    # Destruct the conjunction
    state = tactic_destruct(state, "Hconj")
    
    # Use the left part to prove the goal
    state = tactic_exact(state, "Hconj_left")
    
    assert state.is_complete()

def test_auto_tactic(simple_implication_state):
    """Test auto tactic on simple proof"""
    state = simple_implication_state
    
    # Auto should be able to prove this simple implication
    state = tactic_auto(state)
    
    assert state.is_complete()