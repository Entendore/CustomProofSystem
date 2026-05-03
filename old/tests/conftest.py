import pytest
import sys
from pathlib import Path
from unittest.mock import MagicMock

# Add project directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from proof_assistant import (
    ProofState, ProofTree, parse_formula, parse_term,
    term_repr, prop_repr, tactic_exact, tactic_intro, tactic_split,
    tactic_assumption, tactic_forall_elim, tactic_exists_intro,
    tactic_reflexivity, tactic_contradiction, tactic_left, tactic_right,
    tactic_not_intro, tactic_dne, tactic_auto, tactic_destruct
)

@pytest.fixture
def empty_proof_state():
    """Create a fresh proof state with no goals"""
    return ProofState([], ProofTree())

@pytest.fixture
def simple_implication_state():
    """Create proof state for P → P"""
    goal = parse_formula("P → P")
    state = ProofState([([], goal)])
    state.proof_tree.set_initial_goal(([], goal), "reflexive_implication")
    return state

@pytest.fixture
def conjunction_state():
    """Create proof state for P → Q → P ∧ Q"""
    goal = parse_formula("P → Q → P ∧ Q")
    state = ProofState([([], goal)])
    state.proof_tree.set_initial_goal(([], goal), "conjunction_introduction")
    return state

@pytest.fixture
def quantifier_state():
    """Create proof state for (∀x. P(x)) → P(a)"""
    goal = parse_formula("(∀x. P(x)) → P(a)")
    state = ProofState([([], goal)])
    state.proof_tree.set_initial_goal(([], goal), "forall_elimination")
    return state

@pytest.fixture
def exists_state():
    """Create proof state for P(a) → ∃x. P(x)"""
    goal = parse_formula("P(a) → ∃x. P(x)")
    state = ProofState([([], goal)])
    state.proof_tree.set_initial_goal(([], goal), "exists_introduction")
    return state

@pytest.fixture
def equality_state():
    """Create proof state for ∀x. x = x"""
    goal = parse_formula("∀x. x = x")
    state = ProofState([([], goal)])
    state.proof_tree.set_initial_goal(([], goal), "reflexivity")
    return state

@pytest.fixture
def complex_state():
    """Create proof state for (P → Q) → (Q → R) → P → R"""
    goal = parse_formula("(P → Q) → (Q → R) → P → R")
    state = ProofState([([], goal)])
    state.proof_tree.set_initial_goal(([], goal), "transitivity")
    return state

@pytest.fixture
def negation_state():
    """Create proof state for ¬¬P → P"""
    goal = parse_formula("¬¬P → P")
    state = ProofState([([], goal)])
    state.proof_tree.set_initial_goal(([], goal), "double_negation_elim")
    return state

@pytest.fixture
def disjunction_state():
    """Create proof state for P → P ∨ Q"""
    goal = parse_formula("P → P ∨ Q")
    state = ProofState([([], goal)])
    state.proof_tree.set_initial_goal(([], goal), "disjunction_introduction")
    return state

@pytest.fixture
def contradiction_state():
    """Create proof state with contradiction"""
    # Goal: ⊥ → P (from false, anything follows)
    goal = parse_formula("⊥ → P")
    state = ProofState([([], goal)])
    state.proof_tree.set_initial_goal(([], goal), "ex_falso")
    return state

@pytest.fixture
def temp_dir(tmp_path):
    """Temporary directory for testing file operations"""
    return tmp_path