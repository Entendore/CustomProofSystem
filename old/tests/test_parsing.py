import pytest
from proof_assistant import parse_formula, parse_term, prop_repr, term_repr

def test_basic_propositions():
    """Test parsing basic propositions"""
    assert prop_repr(parse_formula("P")) == "P"
    assert prop_repr(parse_formula("P → Q")) == "P → Q"
    assert prop_repr(parse_formula("P ∧ Q")) == "P ∧ Q"
    assert prop_repr(parse_formula("P ∨ Q")) == "P ∨ Q"
    assert prop_repr(parse_formula("¬P")) == "¬P"
    assert prop_repr(parse_formula("⊥")) == "⊥"

def test_quantifiers():
    """Test parsing quantified formulas"""
    assert prop_repr(parse_formula("∀x. P(x)")) == "∀x. P(x)"
    assert prop_repr(parse_formula("∃x. P(x)")) == "∃x. P(x)"
    assert prop_repr(parse_formula("∀x. P(x) → Q(x)")) == "∀x. P(x) → Q(x)"
    assert prop_repr(parse_formula("∃y. ∀x. R(x, y)")) == "∃y. ∀x. R(x, y)"

def test_equality():
    """Test parsing equality expressions"""
    assert prop_repr(parse_formula("x = y")) == "x = y"
    assert prop_repr(parse_formula("f(x) = g(y)")) == "f(x) = g(y)"
    assert prop_repr(parse_formula("c = d")) == "c = d"

def test_terms():
    """Test parsing terms"""
    assert term_repr(parse_term("x")) == "x"
    assert term_repr(parse_term("f(x,y)")) == "f(x, y)"
    assert term_repr(parse_term("c")) == "c"
    assert term_repr(parse_term("f(g(x), h(y, z))")) == "f(g(x), h(y, z))"

def test_complex_formulas():
    """Test parsing complex formulas"""
    formula = "¬(P ∧ Q) → (¬P ∨ ¬Q)"
    assert prop_repr(parse_formula(formula)) == "¬(P ∧ Q) → (¬P ∨ ¬Q)"
    
    formula = "∀x. (P(x) → ∃y. Q(x, y))"
    assert prop_repr(parse_formula(formula)) == "∀x. P(x) → ∃y. Q(x, y)"
    
    formula = "((P → Q) ∧ (Q → R)) → (P → R)"
    assert prop_repr(parse_formula(formula)) == "(P → Q ∧ Q → R) → P → R"

def test_parentheses_and_precedence():
    """Test operator precedence and parentheses"""
    # Without parentheses: → has lowest precedence
    formula = "P ∧ Q → R"
    assert prop_repr(parse_formula(formula)) == "(P ∧ Q) → R"
    
    # With parentheses
    formula = "P ∧ (Q → R)"
    assert prop_repr(parse_formula(formula)) == "P ∧ (Q → R)"
    
    # Nested implications
    formula = "P → Q → R"
    assert prop_repr(parse_formula(formula)) == "P → Q → R"

def test_error_handling():
    """Test error handling for invalid inputs"""
    with pytest.raises(Exception):
        parse_formula("P ->")  # Incomplete formula
    
    with pytest.raises(Exception):
        parse_formula("P && Q")  # Invalid syntax
    
    with pytest.raises(Exception):
        parse_formula("∀. P(x)")  # Missing variable
    
    with pytest.raises(Exception):
        parse_term("f(,y)")  # Invalid term syntax