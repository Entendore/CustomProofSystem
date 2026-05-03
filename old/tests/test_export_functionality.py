import pytest
import re
import os
import sys
import json
from pathlib import Path
from unittest.mock import MagicMock

# Add project directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from proof_assistant import (
    ProofState, ProofTree, parse_formula, parse_term, prop_repr, term_repr,
    tactic_intro, tactic_exact, tactic_split, tactic_assumption,
    tactic_forall_elim, tactic_exists_intro, tactic_reflexivity,
    tactic_dne, tactic_contradiction, tactic_left, tactic_right,
    tactic_not_intro, Context, Prop, Term, ProofSystem
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

def verify_coq_export(coq_code, theorem_name, expected_tactics=None):
    """Verify Coq export contains expected elements"""
    assert coq_code is not None
    assert theorem_name in coq_code

    # Basic structure checks
    assert "Theorem" in coq_code
    assert "Proof." in coq_code
    assert "Qed." in coq_code

    # Verify tactics if provided
    if expected_tactics:
        for tactic in expected_tactics:
            assert tactic in coq_code

    # Verify it's valid Coq syntax (basic check)
    assert coq_code.count("intros") <= coq_code.count(".")
    assert coq_code.count("exact") <= coq_code.count(".")

def verify_isabelle_export(isabelle_code, theorem_name, expected_methods=None):
    """Verify Isabelle export contains expected elements"""
    assert isabelle_code is not None
    assert theorem_name in isabelle_code

    # Basic structure checks
    assert "theory" in isabelle_code
    assert "imports Main" in isabelle_code
    assert "begin" in isabelle_code
    assert "end" in isabelle_code

    # Theorem structure
    assert "theorem" in isabelle_code

    # Verify methods if provided
    if expected_methods:
        for method in expected_methods:
            assert method in isabelle_code

def verify_lean_export(lean_code, theorem_name, expected_tactics=None):
    """Verify Lean export contains expected elements"""
    assert lean_code is not None
    assert theorem_name in lean_code

    # Basic structure checks
    assert "theorem" in lean_code
    assert "import Mathlib" in lean_code

    # Verify tactics if provided
    if expected_tactics:
        for tactic in expected_tactics:
            assert tactic in lean_code

    # Verify it's valid Lean syntax (basic check)
    assert lean_code.count("intro") <= lean_code.count("\n")
    assert lean_code.count("exact") <= lean_code.count("\n")

def test_simple_implication_export(simple_implication_state, temp_dir):
    """Test Coq export of simple implication proof"""
    state = simple_implication_state

    # Complete the proof
    state = tactic_intro(state, "H")
    state = tactic_exact(state, "H")

    # Export to Coq
    coq_code = state.proof_tree.export_coq()
    verify_coq_export(coq_code, "reflexive_implication", ["intros H", "exact H"])

    # Export to Isabelle
    isabelle_code = state.proof_tree.export_isabelle()
    verify_isabelle_export(isabelle_code, "reflexive_implication", ["assume", "show"])

    # Export to Lean
    lean_code = state.proof_tree.export_lean()
    verify_lean_export(lean_code, "reflexive_implication", ["intro H", "exact H"])

    # Test all export
    exports = state.proof_tree.export_all(str(temp_dir))
    assert "coq" in exports
    assert "isabelle" in exports
    assert "lean" in exports
    assert len(exports["coq"]) > 0
    assert len(exports["isabelle"]) > 0
    assert len(exports["lean"]) > 0

    # Verify files were created
    coq_file = temp_dir / "reflexive_implication.v"
    isabelle_file = temp_dir / "reflexive_implication.thy"
    lean_file = temp_dir / "reflexive_implication.lean"

    assert coq_file.exists()
    assert isabelle_file.exists()
    assert lean_file.exists()

    # Verify file contents
    with open(coq_file, 'r') as f:
        content = f.read()
        assert "Theorem reflexive_implication" in content
        assert "intros H." in content
        assert "exact H." in content
        assert "Qed." in content

    with open(lean_file, 'r') as f:
        content = f.read()
        assert "theorem reflexive_implication" in content
        assert "intro H" in content
        assert "exact H" in content

def test_conjunction_export(conjunction_state, temp_dir):
    """Test export of conjunction proof"""
    state = conjunction_state

    # Complete the proof
    state = tactic_intro(state, "Hp")
    state = tactic_intro(state, "Hq")
    state = tactic_split(state)
    state = tactic_exact(state, "Hp")
    state = tactic_exact(state, "Hq")

    # Export to Coq
    coq_code = state.proof_tree.export_coq()
    verify_coq_export(coq_code, "conjunction_introduction", ["intros Hp", "intros Hq", "split", "exact Hp", "exact Hq"])

    # Export to Isabelle
    isabelle_code = state.proof_tree.export_isabelle()
    verify_isabelle_export(isabelle_code, "conjunction_introduction", ["assume", "thus", "by auto"])

    # Export to Lean
    lean_code = state.proof_tree.export_lean()
    verify_lean_export(lean_code, "conjunction_introduction", ["intro Hp", "intro Hq", "constructor", "exact Hp", "exact Hq"])

    # Verify files were created
    exports = state.proof_tree.export_all(str(temp_dir))
    assert (temp_dir / "conjunction_introduction.v").exists()
    assert (temp_dir / "conjunction_introduction.thy").exists()
    assert (temp_dir / "conjunction_introduction.lean").exists()

def test_quantifier_export(quantifier_state, temp_dir):
    """Test export of quantifier proof"""
    state = quantifier_state

    # Complete the proof
    state = tactic_intro(state, "Hforall")

    # Find the hypothesis index for "Hforall"
    ctx, _ = state.current()
    hyp_idx = next(i for i, (name, _) in enumerate(ctx) if name == "Hforall")

    state = tactic_forall_elim(state, hyp_idx, parse_term("a"))
    state = tactic_assumption(state)

    # Export to Coq
    coq_code = state.proof_tree.export_coq()
    verify_coq_export(coq_code, "forall_elimination", ["intros Hforall", "specialize", "assumption"])

    # Export to Isabelle
    isabelle_code = state.proof_tree.export_isabelle()
    verify_isabelle_export(isabelle_code, "forall_elimination", ["assume", "have", "by auto"])

    # Export to Lean
    lean_code = state.proof_tree.export_lean()
    verify_lean_export(lean_code, "forall_elimination", ["intro Hforall", "specialize", "assumption"])

    # Verify files were created
    exports = state.proof_tree.export_all(str(temp_dir))
    assert (temp_dir / "forall_elimination.v").exists()
    assert (temp_dir / "forall_elimination.thy").exists()
    assert (temp_dir / "forall_elimination.lean").exists()

def test_equality_export(equality_state, temp_dir):
    """Test export of equality proof"""
    state = equality_state

    # Complete the proof
    state = tactic_intro(state, "x")
    state = tactic_reflexivity(state)

    # Export to Coq
    coq_code = state.proof_tree.export_coq()
    verify_coq_export(coq_code, "reflexivity", ["intros x", "reflexivity"])

    # Export to Isabelle
    isabelle_code = state.proof_tree.export_isabelle()
    verify_isabelle_export(isabelle_code, "reflexivity", ["assume", "by simp"])

    # Export to Lean
    lean_code = state.proof_tree.export_lean()
    verify_lean_export(lean_code, "reflexivity", ["intro x", "reflexivity"])

    # Verify files were created
    exports = state.proof_tree.export_all(str(temp_dir))
    assert (temp_dir / "reflexivity.v").exists()
    assert (temp_dir / "reflexivity.thy").exists()
    assert (temp_dir / "reflexivity.lean").exists()

def test_exists_export(exists_state, temp_dir):
    """Test export of existential quantifier proof"""
    state = exists_state

    # Complete the proof
    state = tactic_intro(state, "Hpa")
    state = tactic_exists_intro(state, parse_term("a"))
    state = tactic_assumption(state)

    # Export to Coq
    coq_code = state.proof_tree.export_coq()
    verify_coq_export(coq_code, "exists_introduction", ["intros Hpa", "exists a", "assumption"])

    # Export to Isabelle
    isabelle_code = state.proof_tree.export_isabelle()
    verify_isabelle_export(isabelle_code, "exists_introduction", ["assume", "thus", "by (rule exI)"])

    # Export to Lean
    lean_code = state.proof_tree.export_lean()
    verify_lean_export(lean_code, "exists_introduction", ["intro Hpa", "use a", "assumption"])

    # Verify files were created
    exports = state.proof_tree.export_all(str(temp_dir))
    assert (temp_dir / "exists_introduction.v").exists()
    assert (temp_dir / "exists_introduction.thy").exists()
    assert (temp_dir / "exists_introduction.lean").exists()

def test_negation_export(negation_state, temp_dir):
    """Test export of negation proof"""
    state = negation_state

    # Complete the proof
    state = tactic_intro(state, "Hnnp")
    state = tactic_dne(state, "Hnnp")

    # Export to Coq
    coq_code = state.proof_tree.export_coq()
    verify_coq_export(coq_code, "double_negation_elim", ["intros Hnnp", "apply NNPP in Hnnp", "exact Hnnp"])

    # Export to Isabelle
    isabelle_code = state.proof_tree.export_isabelle()
    verify_isabelle_export(isabelle_code, "double_negation_elim", ["assume", "by (rule notnotD)"])

    # Export to Lean
    lean_code = state.proof_tree.export_lean()
    verify_lean_export(lean_code, "double_negation_elim", ["intro Hnnp", "by_contra! Hnnp", "exact Hnnp"])

    # Verify files were created
    exports = state.proof_tree.export_all(str(temp_dir))
    assert (temp_dir / "double_negation_elim.v").exists()
    assert (temp_dir / "double_negation_elim.thy").exists()
    assert (temp_dir / "double_negation_elim.lean").exists()

def test_contradiction_export(contradiction_state, temp_dir):
    """Test export of contradiction proof"""
    state = contradiction_state

    # Complete the proof
    state = tactic_intro(state, "Hfalse")
    state = tactic_contradiction(state)

    # Export to Coq
    coq_code = state.proof_tree.export_coq()
    verify_coq_export(coq_code, "ex_falso", ["intros Hfalse", "contradiction"])

    # Export to Isabelle
    isabelle_code = state.proof_tree.export_isabelle()
    verify_isabelle_export(isabelle_code, "ex_falso", ["assume", "by contradiction"])

    # Export to Lean
    lean_code = state.proof_tree.export_lean()
    verify_lean_export(lean_code, "ex_falso", ["intro Hfalse", "contradiction"])

    # Verify files were created
    exports = state.proof_tree.export_all(str(temp_dir))
    assert (temp_dir / "ex_falso.v").exists()
    assert (temp_dir / "ex_falso.thy").exists()
    assert (temp_dir / "ex_falso.lean").exists()

def test_disjunction_export(disjunction_state, temp_dir):
    """Test export of disjunction proof"""
    state = disjunction_state

    # Complete the proof
    state = tactic_intro(state, "H")
    state = tactic_left(state)
    state = tactic_exact(state, "H")

    # Export to Coq
    coq_code = state.proof_tree.export_coq()
    verify_coq_export(coq_code, "disjunction_introduction", ["intros H", "left", "exact H"])

    # Export to Isabelle
    isabelle_code = state.proof_tree.export_isabelle()
    verify_isabelle_export(isabelle_code, "disjunction_introduction", ["assume", "thus", "by (rule disjI1)"])

    # Export to Lean
    lean_code = state.proof_tree.export_lean()
    verify_lean_export(lean_code, "disjunction_introduction", ["intro H", "left", "exact H"])

    # Verify files were created
    exports = state.proof_tree.export_all(str(temp_dir))
    assert (temp_dir / "disjunction_introduction.v").exists()
    assert (temp_dir / "disjunction_introduction.thy").exists()
    assert (temp_dir / "disjunction_introduction.lean").exists()

def test_complex_proof_export(complex_state, temp_dir):
    """Test export of complex proof"""
    state = complex_state

    # Complete the proof
    state = tactic_intro(state, "H1") # P → Q
    state = tactic_intro(state, "H2") # Q → R
    state = tactic_intro(state, "H3") # P
    state = tactic_exact(state, "H2") # Need to prove Q
    state = tactic_exact(state, "H1") # Need to prove P
    state = tactic_exact(state, "H3") # Prove P

    # Export to Coq
    coq_code = state.proof_tree.export_coq()
    verify_coq_export(coq_code, "transitivity", ["intros H1", "intros H2", "intros H3", "exact H2", "exact H1", "exact H3"])

    # Export to Isabelle
    isabelle_code = state.proof_tree.export_isabelle()
    verify_isabelle_export(isabelle_code, "transitivity", ["assume", "then show", "by auto"])

    # Export to Lean
    lean_code = state.proof_tree.export_lean()
    verify_lean_export(lean_code, "transitivity", ["intro H1", "intro H2", "intro H3", "exact H2", "exact H1", "exact H3"])

    # Verify files were created
    exports = state.proof_tree.export_all(str(temp_dir))
    assert (temp_dir / "transitivity.v").exists()
    assert (temp_dir / "transitivity.thy").exists()
    assert (temp_dir / "transitivity.lean").exists()

def test_export_options(simple_implication_state, temp_dir):
    """Test customizing export options"""
    state = simple_implication_state

    # Complete the proof
    state = tactic_intro(state, "H")
    state = tactic_exact(state, "H")

    # Customize Coq export options
    state.proof_tree.export_options[ProofSystem.COQ] = {
        "use_ssr": True,
        "indent": 4,
        "include_imports": False
    }

    # Export to Coq with custom options
    coq_code = state.proof_tree.export_coq()

    # Verify custom options affected the export
    assert "Theorem reflexive_implication :" in coq_code
    assert "Proof." in coq_code
    assert "Qed." in coq_code
    assert "Require Import" not in coq_code # No imports included
    assert " intros H." in coq_code # 4-space indentation

    # Customize Isabelle export options
    state.proof_tree.export_options[ProofSystem.ISABELLE] = {
        "theory_name": "Custom_Theory",
        "indent": 4,
        "include_headers": False
    }

    # Export to Isabelle with custom options
    isabelle_code = state.proof_tree.export_isabelle()

    # Verify custom options affected the export
    assert "theorem reflexive_implication" in isabelle_code
    assert "proof -" in isabelle_code
    assert "qed" in isabelle_code
    assert "theory Custom_Theory" not in isabelle_code # No headers included
    assert " assume" in isabelle_code # 4-space indentation

    # Customize Lean export options
    state.proof_tree.export_options[ProofSystem.LEAN] = {
        "use_structured_proofs": False,
        "indent": 4,
        "include_imports": False
    }

    # Export to Lean with custom options
    lean_code = state.proof_tree.export_lean()

    # Verify custom options affected the export
    assert "theorem reflexive_implication" in lean_code
    assert "by sorry" in lean_code # Term mode proof
    assert "import Mathlib" not in lean_code # No imports included
    assert " sorry" in lean_code # 4-space indentation

def test_save_load_export_state(simple_implication_state, temp_dir):
    """Test saving and loading proof state with export information"""
    state = simple_implication_state

    # Complete the proof
    state = tactic_intro(state, "H")
    state = tactic_exact(state, "H")

    # Customize export options
    state.proof_tree.export_options[ProofSystem.COQ]["use_ssr"] = True
    state.proof_tree.theorem_name = "custom_theorem_name"

    # Save proof state
    state_file = temp_dir / "proof_state.json"
    state.proof_tree.save_proof_state(str(state_file))

    # Verify file exists and contains proper data
    assert state_file.exists()
    with open(state_file, 'r') as f:
        data = json.load(f)
    assert data["theorem_name"] == "custom_theorem_name"
    assert "export_options" in data
    assert "coq" in data["export_options"]
    assert data["export_options"]["coq"]["use_ssr"] is True

    # Load proof state
    new_tree = ProofTree()
    new_tree.load_proof_state(str(state_file))

    # Verify loaded state has correct export options
    assert new_tree.theorem_name == "custom_theorem_name"
    assert new_tree.export_options[ProofSystem.COQ]["use_ssr"] is True

    # Export using loaded state
    new_state = ProofState([], new_tree)
    coq_code = new_tree.export_coq()
    assert "custom_theorem_name" in coq_code

def test_proof_with_context_export(temp_dir):
    """Test export of proof with hypotheses in context"""
    # Goal: P → (P → Q) → Q
    goal = parse_formula("P → (P → Q) → Q")
    state = ProofState([([], goal)])
    state.proof_tree.set_initial_goal(([], goal), "modus_ponens")

    # Build the proof
    state = tactic_intro(state, "Hp") # Assume P
    state = tactic_intro(state, "Himp") # Assume P → Q

    # Apply the implication to get Q
    state = tactic_exact(state, "Himp") # Need to prove P
    state = tactic_exact(state, "Hp") # Prove P using hypothesis

    # Verify proof is complete
    assert state.is_complete()

    # Export to all systems
    exports = state.proof_tree.export_all(str(temp_dir))

    # Verify Coq export
    coq_code = exports["coq"]
    assert "Theorem modus_ponens" in coq_code
    assert "intros Hp Himp." in coq_code
    assert "exact Himp." in coq_code
    assert "exact Hp." in coq_code

    # Verify Isabelle export
    isabelle_code = exports["isabelle"]
    assert "theorem modus_ponens" in isabelle_code
    assert "assumes" in isabelle_code
    assert "shows" in isabelle_code
    assert "assume Hp:" in isabelle_code
    assert "assume Himp:" in isabelle_code

    # Verify Lean export
    lean_code = exports["lean"]
    assert "theorem modus_ponens" in lean_code
    assert "(Hp : P) (Himp : P → Q)" in lean_code
    assert "exact Himp" in lean_code
    assert "exact Hp" in lean_code

    # Verify files were created
    assert (temp_dir / "modus_ponens.v").exists()
    assert (temp_dir / "modus_ponens.thy").exists()
    assert (temp_dir / "modus_ponens.lean").exists()