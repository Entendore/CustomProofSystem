import re
import os
import sys
import json
import logging
import datetime
from typing import List, Tuple, Optional, Dict, Any, Union, Set
from dataclasses import dataclass, field
from enum import Enum
from copy import deepcopy
from pathlib import Path
from functools import wraps

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s',
    handlers=[
        logging.FileHandler("proof_assistant.log"),
        logging.StreamHandler(sys.stdout)
    ]
)
logger = logging.getLogger("ProofAssistant")

# === Type Definitions ===
Term = Union[
    Tuple[str, str],                         # ("var", name)
    Tuple[str, str],                         # ("const", name)
    Tuple[str, str, List['Term']],           # ("fun", name, args)
    Tuple[str, List[str], 'Term'],           # ("lambda", [params], body)
    Tuple[str, 'Term', 'Term'],              # ("app", function_term, argument_term)
]
Prop = Union[
    Tuple[str, str],                         # ("var", x) or ("const", c)
    Tuple[str],                              # ("bottom",)
    Tuple[str, str, List[Term]],             # ("pred", name, args)
    Tuple[str, 'Prop', 'Prop'],              # "implies", "and", "or"
    Tuple[str, 'Prop'],                      # "not"
    Tuple[str, str, 'Prop'],                 # "forall", "exists"
]
Context = List[Tuple[str, Prop]]
Goal = Tuple[Context, Prop]
ProofStateSnapshot = Tuple[List[Goal], List['ProofStep']]

class ProofSystem(Enum):
    COQ = "coq"
    ISABELLE = "isabelle"
    LEAN = "lean"

@dataclass
class ProofStep:
    tactic_name: str
    arguments: List[Any]
    subgoals_before: List[Goal]
    subgoals_after: List[Goal]
    timestamp: datetime.datetime = field(default_factory=datetime.datetime.now)
    success: bool = True
    error_message: Optional[str] = None

class ProofTree:
    def __init__(self):
        self.steps: List[ProofStep] = []
        self.initial_goal: Optional[Goal] = None
        self.theorem_name: str = "theorem"
        self.export_options: Dict[ProofSystem, Dict] = {
            ProofSystem.COQ: {"indent": 2, "include_imports": True},
            ProofSystem.ISABELLE: {"theory_name": "My_Theory", "indent": 2, "include_headers": True},
            ProofSystem.LEAN: {"use_structured_proofs": True, "indent": 2, "include_imports": True}
        }

    def record_step(self, tactic_name: str, arguments: List[Any], 
                   state_before: 'ProofState', state_after: 'ProofState',
                   success: bool = True, error_message: Optional[str] = None):
        step = ProofStep(
            tactic_name=tactic_name, arguments=arguments,
            subgoals_before=deepcopy(state_before.goals),
            subgoals_after=deepcopy(state_after.goals),
            success=success, error_message=error_message
        )
        self.steps.append(step)
        logger.info(f"Recorded step: {tactic_name} | Success: {success}")

    def set_initial_goal(self, goal: Goal, theorem_name: str = "theorem"):
        self.initial_goal = deepcopy(goal)
        self.theorem_name = theorem_name

    def pretty_print(self) -> str:
        if not self.steps:
            return "No proof steps recorded"
        lines = ["Proof steps:"]
        for i, step in enumerate(self.steps):
            status = "✓" if step.success else "✗"
            lines.append(f"{i+1}. [{status}] {step.tactic_name} {step.arguments}")
        return "\n".join(lines)

    def export_coq(self) -> str:
        if not self.initial_goal or not self.steps: return ""
        indent = " " * self.export_options[ProofSystem.COQ]["indent"]
        lines = []
        if self.export_options[ProofSystem.COQ]["include_imports"]:
            lines.append("Require Import Coq.Logic.Classical_Prop.\n")
        
        ctx, goal = self.initial_goal
        hyps = " ".join([f"({n} : {prop_to_coq(f)})" for n, f in ctx])
        lines.append(f"Theorem {self.theorem_name} {hyps} : {prop_to_coq(goal)}.")
        lines.append("Proof.")
        
        for step in self.steps:
            if not step.success: continue
            cmd = tactic_to_coq(step.tactic_name, step.arguments)
            if cmd: lines.append(f"{indent}{cmd}.")
        lines.append("Qed.")
        return "\n".join(lines)

    def export_isabelle(self) -> str:
        if not self.initial_goal or not self.steps: return ""
        indent = " " * self.export_options[ProofSystem.ISABELLE]["indent"]
        lines = []
        if self.export_options[ProofSystem.ISABELLE]["include_headers"]:
            lines.extend([f"theory {self.export_options[ProofSystem.ISABELLE]['theory_name']}", "  imports Main", "begin", ""])
        
        ctx, goal = self.initial_goal
        theorem_header = f"theorem {self.theorem_name}"
        lines.append(f"{theorem_header}: \"{prop_to_isabelle(goal)}\"")
        lines.append("proof -")
        
        for step in self.steps:
            if not step.success: continue
            cmd = tactic_to_isabelle(step.tactic_name, step.arguments)
            if cmd: lines.append(f"{indent}{cmd}")
        lines.append(f"{indent}qed")
        if self.export_options[ProofSystem.ISABELLE]["include_headers"]:
            lines.append("\nend")
        return "\n".join(lines)

    def export_lean(self) -> str:
        if not self.initial_goal or not self.steps: return ""
        indent = " " * self.export_options[ProofSystem.LEAN]["indent"]
        lines = []
        if self.export_options[ProofSystem.LEAN]["include_imports"]:
            lines.extend(["import Mathlib", "import Mathlib.Tactic", ""])
        
        ctx, goal = self.initial_goal
        lines.append(f"theorem {self.theorem_name} : {prop_to_lean(goal)} := by")
        
        for step in self.steps:
            if not step.success: continue
            cmd = tactic_to_lean(step.tactic_name, step.arguments)
            if cmd: lines.append(f"{indent}{cmd}")
        return "\n".join(lines)

    def save_proof_state(self, filename: str):
        state = {
            "theorem_name": self.theorem_name,
            "initial_goal": self.initial_goal,
            "steps": [{"name": s.tactic_name, "args": s.arguments, "ts": s.timestamp.isoformat()} for s in self.steps]
        }
        with open(filename, "w") as f:
            json.dump(state, f, indent=2)

class ProofState:
    def __init__(self, goals: List[Goal], proof_tree: Optional[ProofTree] = None):
        self.goals = goals
        self.proof_tree = proof_tree or ProofTree()
        self.history: List[ProofStateSnapshot] = []
        self.future: List[ProofStateSnapshot] = []

    def current(self) -> Optional[Goal]:
        return self.goals[-1] if self.goals else None

    def is_complete(self) -> bool:
        return not self.goals

    def add_subgoals(self, new_goals: List[Goal]) -> 'ProofState':
        new_state = ProofState(self.goals[:-1] + new_goals, self.proof_tree)
        self.history.append((deepcopy(self.goals), deepcopy(self.proof_tree.steps)))
        self.future.clear()
        return new_state

    def undo(self) -> Optional['ProofState']:
        if not self.history: return None
        self.future.append((deepcopy(self.goals), deepcopy(self.proof_tree.steps)))
        prev_goals, prev_steps = self.history.pop()
        new_state = ProofState(deepcopy(prev_goals), deepcopy(self.proof_tree))
        new_state.proof_tree.steps = deepcopy(prev_steps)
        new_state.history = self.history.copy()
        new_state.future = self.future.copy()
        return new_state

    def redo(self) -> Optional['ProofState']:
        if not self.future: return None
        self.history.append((deepcopy(self.goals), deepcopy(self.proof_tree.steps)))
        next_goals, next_steps = self.future.pop()
        new_state = ProofState(deepcopy(next_goals), deepcopy(self.proof_tree))
        new_state.proof_tree.steps = deepcopy(next_steps)
        new_state.history = self.history.copy()
        new_state.future = self.future.copy()
        return new_state

    def __str__(self):
        if self.is_complete(): return "✅ Proof complete."
        lines = [f"Proof state: {len(self.goals)} remaining goal(s)", "=" * 40]
        for i, (ctx, goal) in enumerate(reversed(self.goals)):
            marker = ">>> " if i == 0 else "    "
            lines.append(f"{marker}Goal {len(self.goals)-i}:")
            lines.append(pretty_goal(ctx, goal))
        return "\n".join(lines)

# === Term/Prop Constructors & Utils ===
def fun(name: str, args: List[Term]) -> Term: return ("fun", name, args)
def var(name: str) -> Term: return ("var", name)
def const(name: str) -> Term: return ("const", name)
def pred(name: str, args: List[Term]) -> Prop: return ("pred", name, args)
def implies(p: Prop, q: Prop) -> Prop: return ("implies", p, q)
def and_(p: Prop, q: Prop) -> Prop: return ("and", p, q)
def or_(p: Prop, q: Prop) -> Prop: return ("or", p, q)
def not_(p: Prop) -> Prop: return ("not", p)
def forall(varname: str, body: Prop) -> Prop: return ("forall", varname, body)
def exists(varname: str, body: Prop) -> Prop: return ("exists", varname, body)
def bottom() -> Prop: return ("bottom",)
def eq(t1: Term, t2: Term) -> Prop: return pred("=", [t1, t2])
def iff(p: Prop, q: Prop) -> Prop: return and_(implies(p, q), implies(q, p))

def prop_repr(f: Prop) -> str:
    match f:
        case ('not', p): return f"¬{prop_repr_paren(p)}"
        case ('and', p, q): return f"{prop_repr_paren(p)} ∧ {prop_repr_paren(q)}"
        case ('or', p, q): return f"{prop_repr_paren(p)} ∨ {prop_repr_paren(q)}"
        case ('implies', p, q): return f"{prop_repr_paren(p)} → {prop_repr(q)}"
        case ('forall', v, body): return f"∀{v}. {prop_repr(body)}"
        case ('exists', v, body): return f"∃{v}. {prop_repr(body)}"
        case ('bottom',): return "⊥"
        case ('pred', name, args): 
            if name == "=" and len(args) == 2: return f"{term_repr(args[0])} = {term_repr(args[1])}"
            return f"{name}({', '.join(term_repr(a) for a in args)})"
        case ('var', x): return x
        case ('const', c): return c
        case _: return str(f)

def prop_repr_paren(f: Prop) -> str:
    if isinstance(f, tuple) and f[0] in {"and", "or", "implies"}: return f"({prop_repr(f)})"
    return prop_repr(f)

def term_repr(t: Term) -> str:
    match t:
        case ("var", x): return x
        case ("const", c): return c
        case ("fun", name, args): return f"{name}({', '.join(term_repr(a) for a in args)})"
        case ("lambda", params, body): return f"(λ{','.join(params)}. {term_repr(body)})"
        case ("app", f, a): return f"({term_repr(f)} {term_repr(a)})"
        case _: return str(t)

def pretty_context(ctx: Context) -> str:
    if not ctx: return "  Context: ∅"
    maxlen = max(len(name) for name, _ in ctx) if ctx else 0
    lines = [f"  {name.ljust(maxlen)} : {prop_repr(formula)}" for name, formula in ctx]
    return "  Context:\n" + "\n".join(lines)

def pretty_goal(ctx: Context, goal: Prop) -> str:
    return f"{pretty_context(ctx)}\n  Goal: {prop_repr(goal)}"

# === Substitution, Free Vars, Alpha Eq ===
def fresh_var(existing: set) -> str:
    base = "x"; i = 1
    while f"{base}{i}" in existing: i += 1
    return f"{base}{i}"

def free_vars(prop: Prop) -> Set[str]:
    match prop:
        case ('var', x): return {x}
        case ('const', _): return set()
        case ('pred', _, args): return set().union(*(free_vars_term(a) for a in args))
        case ('not', p): return free_vars(p)
        case ('and' | 'or' | 'implies', p, q): return free_vars(p) | free_vars(q)
        case ('forall' | 'exists', v, body): return free_vars(body) - {v}
        case ('bottom',): return set()
        case _: return set()

def free_vars_term(t: Term) -> Set[str]:
    match t:
        case ('var', x): return {x}
        case ('const', _): return set()
        case ('fun', _, args): return set().union(*(free_vars_term(a) for a in args))
        case ('lambda', params, body): return free_vars_term(body) - set(params)
        case ('app', f, a): return free_vars_term(f) | free_vars_term(a)
        case _: return set()

def substitute(prop: Prop, varname: str, term: Term) -> Prop:
    match prop:
        case ('pred', name, args): return ('pred', name, [subst_term(a, varname, term) for a in args])
        case ('not', p): return ('not', substitute(p, varname, term))
        case ('and' | 'or' | 'implies' as tag, p, q): return (tag, substitute(p, varname, term), substitute(q, varname, term))
        case ('forall' | 'exists' as tag, v, body):
            if v == varname: return (tag, v, body)
            if v in free_vars_term(term):
                fresh = fresh_var(free_vars(body) | free_vars_term(term))
                return (tag, fresh, substitute(substitute_var(body, v, fresh), varname, term))
            return (tag, v, substitute(body, varname, term))
        case _: return prop

def substitute_var(prop: Prop, old: str, new: str) -> Prop:
    match prop:
        case ('var', x): return ('var', new) if x == old else prop
        case ('forall' | 'exists' as tag, v, body):
            if v == old: return prop
            return (tag, v, substitute_var(body, old, new))
        case _: return prop

def subst_term(t: Term, varname: str, replacement: Term) -> Term:
    match t:
        case ('var', x): return replacement if x == varname else t
        case ('fun', name, args): return ('fun', name, [subst_term(a, varname, replacement) for a in args])
        case _: return t

def alpha_eq(p1: Prop, p2: Prop) -> bool:
    match p1, p2:
        case ("forall", v1, b1), ("forall", v2, b2):
            fresh = fresh_var(free_vars(b1) | free_vars(b2))
            return alpha_eq(substitute_var(b1, v1, fresh), substitute_var(b2, v2, fresh))
        case ("exists", v1, b1), ("exists", v2, b2):
            fresh = fresh_var(free_vars(b1) | free_vars(b2))
            return alpha_eq(substitute_var(b1, v1, fresh), substitute_var(b2, v2, fresh))
        case (tag1, *args1), (tag2, *args2) if tag1 == tag2:
            return all(alpha_eq(x, y) for x, y in zip(args1, args2))
        case _: return p1 == p2

def term_eq(t1: Term, t2: Term) -> bool:
    match t1, t2:
        case ('var', x1), ('var', x2): return x1 == x2
        case ('const', c1), ('const', c2): return c1 == c2
        case ('fun', n1, args1), ('fun', n2, args2): return n1 == n2 and len(args1) == len(args2) and all(term_eq(a1, a2) for a1, a2 in zip(args1, args2))
        case _: return False

# === Tactics ===
def proof_tactic(func):
    @wraps(func)
    def wrapper(state: ProofState, *args, **kwargs) -> ProofState:
        state_before = ProofState(deepcopy(state.goals), state.proof_tree)
        try:
            result = func(state, *args, **kwargs)
            result.history = state.history.copy()
            result.future = state.future.copy()
            state.proof_tree.record_step(func.__name__, list(args), state_before, result, success=True)
            return result
        except Exception as e:
            state.proof_tree.record_step(func.__name__, list(args), state_before, state, success=False, error_message=str(e))
            raise
    return wrapper

@proof_tactic
def tactic_intro(state: ProofState, name: str = "H") -> ProofState:
    current = state.current()
    if not current: raise ValueError("No current goal")
    ctx, goal = current
    if goal[0] == "implies":
        return state.add_subgoals([(ctx + [(name, goal[1])], goal[2])])
    elif goal[0] == "forall":
        v, body = goal[1], goal[2]
        fresh = fresh_var(free_vars(body) | {n for n, _ in ctx})
        return state.add_subgoals([(ctx, substitute(body, v, var(fresh)))])
    raise ValueError(f"intro failed: goal is {goal[0]}")

@proof_tactic
def tactic_exact(state: ProofState, term: Union[str, Prop]) -> ProofState:
    current = state.current()
    if not current: raise ValueError("No current goal")
    ctx, goal = current
    if isinstance(term, str):
        hyp = next((f for n, f in ctx if n == term), None)
        if not hyp: raise ValueError(f"Hypothesis {term} not found")
        if alpha_eq(hyp, goal): return ProofState(state.goals[:-1], state.proof_tree)
        raise ValueError(f"Hypothesis {term} does not match goal")
    if alpha_eq(term, goal): return ProofState(state.goals[:-1], state.proof_tree)
    raise ValueError("Formula does not match goal")

@proof_tactic
def tactic_split(state: ProofState) -> ProofState:
    current = state.current()
    if not current: raise ValueError("No current goal")
    ctx, goal = current
    if goal[0] == "and":
        return state.add_subgoals([(ctx, goal[1]), (ctx, goal[2])])
    raise ValueError("split failed: goal is not conjunction")

@proof_tactic
def tactic_left(state: ProofState) -> ProofState:
    current = state.current()
    if not current: raise ValueError("No current goal")
    ctx, goal = current
    if goal[0] == "or": return state.add_subgoals([(ctx, goal[1])])
    raise ValueError("left failed: goal is not disjunction")

@proof_tactic
def tactic_right(state: ProofState) -> ProofState:
    current = state.current()
    if not current: raise ValueError("No current goal")
    ctx, goal = current
    if goal[0] == "or": return state.add_subgoals([(ctx, goal[2])])
    raise ValueError("right failed: goal is not disjunction")

@proof_tactic
def tactic_assumption(state: ProofState) -> ProofState:
    current = state.current()
    if not current: raise ValueError("No current goal")
    ctx, goal = current
    for name, hyp in ctx:
        if alpha_eq(hyp, goal): return ProofState(state.goals[:-1], state.proof_tree)
    raise ValueError("assumption failed: no matching hypothesis")

@proof_tactic
def tactic_reflexivity(state: ProofState) -> ProofState:
    current = state.current()
    if not current: raise ValueError("No current goal")
    ctx, goal = current
    if goal[0] == "pred" and goal[1] == "=" and len(goal[2]) == 2:
        if term_eq(goal[2][0], goal[2][1]): return ProofState(state.goals[:-1], state.proof_tree)
    raise ValueError("reflexivity failed: goal is not t = t")

@proof_tactic
def tactic_exists_intro(state: ProofState, term_str: str) -> ProofState:
    current = state.current()
    if not current: raise ValueError("No current goal")
    ctx, goal = current
    if goal[0] != "exists": raise ValueError("Goal is not existential")
    term = parse_term(term_str) 
    new_goal = substitute(goal[2], goal[1], term)
    return state.add_subgoals([(ctx, new_goal)])

@proof_tactic
def tactic_forall_elim(state: ProofState, hyp_name: str, term_str: str) -> ProofState:
    current = state.current()
    if not current: raise ValueError("No current goal")
    ctx, goal = current
    hyp = next((f for n, f in ctx if n == hyp_name), None)
    if not hyp or hyp[0] != "forall": raise ValueError("Hypothesis not found or not universal")
    term = parse_term(term_str)
    new_prop = substitute(hyp[2], hyp[1], term)
    return state.add_subgoals([(ctx + [(f"{hyp_name}_inst", new_prop)], goal)])

@proof_tactic
def tactic_destruct(state: ProofState, name: str) -> ProofState:
    current = state.current()
    if not current: raise ValueError("No current goal")
    ctx, goal = current
    idx = next((i for i, (n, f) in enumerate(ctx) if n == name), -1)
    if idx == -1: raise ValueError("Hypothesis not found")
    hyp = ctx[idx][1]
    pre, post = ctx[:idx], ctx[idx+1:]
    if hyp[0] == "and":
        return state.add_subgoals([(pre + [(f"{name}_l", hyp[1]), (f"{name}_r", hyp[2])] + post, goal)])
    if hyp[0] == "or":
        return state.add_subgoals([
            (pre + [(f"{name}_l", hyp[1])] + post, goal),
            (pre + [(f"{name}_r", hyp[2])] + post, goal)
        ])
    raise ValueError("Destruct failed: not a conjunction or disjunction")

# === Parser ===
token_specification = [
    ('FORALL',   r'∀|forall'), ('EXISTS',   r'∃|exists'), ('NOT',      r'¬|~|not'),
    ('BOTTOM',   r'⊥|bottom'), ('AND',      r'∧|&|and'), ('OR',       r'∨|\||or'),
    ('IMPLIES',  r'→|->|implies'), ('IFF',      r'↔|<=>|iff'), ('EQ',       r'='),
    ('DOT',      r'\.'), ('LPAREN',   r'\('), ('RPAREN',   r'\)'), ('COMMA',    r','),
    ('LAMBDA',   r'λ|lambda'), ('VAR',      r'[a-z][a-zA-Z0-9_]*'), ('CONST',    r'[A-Z][a-zA-Z0-9_]*'),
    ('SKIP',     r'[ \t\n]+'), ('MISMATCH', r'.'),
]
token_re = re.compile('|'.join(f'(?P<{name}>{pattern})' for name, pattern in token_specification))

def lex(characters: str) -> List[Tuple[str, str]]:
    tokens = []
    for mo in token_re.finditer(characters):
        kind = mo.lastgroup
        value = mo.group()
        if kind == 'SKIP': continue
        elif kind == 'MISMATCH': raise SyntaxError(f'Unknown char {value!r}')
        tokens.append((kind, value))
    return tokens

class Parser:
    def __init__(self, tokens: List[Tuple[str, str]]):
        self.tokens = tokens
        self.pos = 0

    def peek(self): return self.tokens[self.pos] if self.pos < len(self.tokens) else None
    def consume(self, expected=None):
        tok = self.peek()
        if not tok: raise SyntaxError("Unexpected end")
        if expected and tok[0] != expected: raise SyntaxError(f"Expected {expected}, got {tok[0]}")
        self.pos += 1
        return tok

    def parse(self) -> Prop:
        res = self.parse_implication()
        if self.peek(): raise SyntaxError("Unexpected token at end")
        return res

    def parse_implication(self) -> Prop:
        left = self.parse_or()
        if self.peek() and self.peek()[0] == 'IMPLIES':
            self.consume('IMPLIES')
            return implies(left, self.parse_implication()) # Right associative
        return left

    def parse_or(self) -> Prop:
        left = self.parse_and()
        while self.peek() and self.peek()[0] == 'OR':
            self.consume('OR'); left = or_(left, self.parse_and())
        return left

    def parse_and(self) -> Prop:
        left = self.parse_not()
        while self.peek() and self.peek()[0] == 'AND':
            self.consume('AND'); left = and_(left, self.parse_not())
        return left

    def parse_not(self) -> Prop:
        if self.peek() and self.peek()[0] == 'NOT':
            self.consume('NOT'); return not_(self.parse_not())
        return self.parse_quantifier_or_atomic()

    def parse_quantifier_or_atomic(self) -> Prop:
        tok = self.peek()
        if tok and tok[0] == 'FORALL':
            self.consume('FORALL'); v = self.consume('VAR')[1]; self.consume('DOT')
            return forall(v, self.parse_implication())
        if tok and tok[0] == 'EXISTS':
            self.consume('EXISTS'); v = self.consume('VAR')[1]; self.consume('DOT')
            return exists(v, self.parse_implication())
        return self.parse_atomic()

    def parse_atomic(self) -> Prop:
        tok = self.peek()
        if not tok: raise SyntaxError("Unexpected end")
        if tok[0] == 'LPAREN':
            self.consume('LPAREN'); p = self.parse_implication(); self.consume('RPAREN'); return p
        if tok[0] == 'BOTTOM': self.consume('BOTTOM'); return bottom()
        if tok[0] == 'CONST':
            name = self.consume('CONST')[1]
            if self.peek() and self.peek()[0] == 'LPAREN': return pred(name, self.parse_term_list())
            return pred(name, [])
        if tok[0] == 'VAR': 
             return var(self.consume('VAR')[1])
        raise SyntaxError(f"Unexpected token {tok[1]}")

    def parse_term_list(self) -> List[Term]:
        self.consume('LPAREN')
        terms = [self.parse_term()]
        while self.peek() and self.peek()[0] == 'COMMA':
            self.consume('COMMA'); terms.append(self.parse_term())
        self.consume('RPAREN')
        return terms

    def parse_term(self) -> Term:
        tok = self.peek()
        if not tok: raise SyntaxError("Unexpected end in term")
        if tok[0] == 'VAR': return var(self.consume('VAR')[1])
        if tok[0] == 'CONST':
            n = self.consume('CONST')[1]
            if self.peek() and self.peek()[0] == 'LPAREN': return fun(n, self.parse_term_list())
            return const(n)
        if tok[0] == 'LPAREN':
            self.consume('LPAREN'); t = self.parse_term(); self.consume('RPAREN'); return t
        raise SyntaxError(f"Expected term, got {tok[0]}")

def parse_formula(s: str) -> Prop: return Parser(lex(s)).parse()
def parse_term(s: str) -> Term: return Parser(lex(s)).parse_term()

# === Export Helpers ===
def prop_to_coq(p: Prop) -> str:
    match p:
        case ('not', x): return f"~({prop_to_coq(x)})"
        case ('and', a, b): return f"({prop_to_coq(a)} /\\ {prop_to_coq(b)})"
        case ('or', a, b): return f"({prop_to_coq(a)} \\/ {prop_to_coq(b)})"
        case ('implies', a, b): return f"({prop_to_coq(a)} -> {prop_to_coq(b)})"
        case ('forall', v, b): return f"(forall {v}, {prop_to_coq(b)})"
        case ('exists', v, b): return f"(exists {v}, {prop_to_coq(b)})"
        case ('bottom',): return "False"
        case ('pred', "=", [a, b]): return f"({term_to_coq(a)} = {term_to_coq(b)})"
        case ('pred', n, args): return f"{n} {','.join([term_to_coq(a) for a in args])}"
        case _: return prop_repr(p)

def term_to_coq(t: Term) -> str:
    match t:
        case ("var", x): return x
        case ("const", c): return c
        case ("fun", n, args): return f"{n} {' '.join([term_to_coq(a) for a in args])}"
        case _: return term_repr(t)

def tactic_to_coq(name: str, args: List) -> str:
    map = {"intro": "intros", "exact": "exact", "split": "split", "left": "left", "right": "right", "destruct": "destruct", "assumption": "assumption", "reflexivity": "reflexivity"}
    cmd = map.get(name, name)
    return f"{cmd} {' '.join(map(str, args))}" if args else cmd

def prop_to_isabelle(p: Prop) -> str:
    match p:
        case ('implies', a, b): return f"({prop_to_isabelle(a)} \<longrightarrow> {prop_to_isabelle(b)})"
        case ('and', a, b): return f"({prop_to_isabelle(a)} \<and> {prop_to_isabelle(b)})"
        case _ : return prop_repr(p).replace("∀", "\<forall>").replace("∃", "\<exists>").replace("→", "\<longrightarrow>")

def tactic_to_isabelle(name: str, args: List) -> str:
    return f"apply ({tactic_to_coq(name, args)})"

def prop_to_lean(p: Prop) -> str:
    return prop_repr(p).replace("→", "->").replace("∧", "/\\").replace("∨", "\\/")

def tactic_to_lean(name: str, args: List) -> str:
    return tactic_to_coq(name, args)

# === Command Processor ===
def process_command(state: Optional[ProofState], cmd_str: str) -> Tuple[Optional[ProofState], str]:
    msg = ""
    try:
        parts = cmd_str.strip().split(maxsplit=1)
        if not parts: return state, ""
        cmd, rest = parts[0], (parts[1] if len(parts) > 1 else "")
        
        if cmd == "goal":
            if not rest: return state, "Usage: goal <formula>"
            prop = parse_formula(rest)
            state = ProofState([([], prop)])
            state.proof_tree.set_initial_goal(([], prop))
            msg = f"Goal set: {prop_repr(prop)}"
        elif cmd == "theorem":
            args = rest.split(maxsplit=1)
            if len(args) < 2: return state, "Usage: theorem <name> <formula>"
            name, formula = args[0], args[1]
            prop = parse_formula(formula)
            state = ProofState([([], prop)])
            state.proof_tree.set_initial_goal(([], prop), name)
            msg = f"Theorem {name} set: {prop_repr(prop)}"
        elif state is None:
            msg = "No active proof. Use 'goal' or 'theorem'."
        else:
            if cmd == "intro":
                state = tactic_intro(state, rest if rest else None)
            elif cmd == "exact":
                state = tactic_exact(state, rest)
            elif cmd == "split":
                state = tactic_split(state)
            elif cmd == "left":
                state = tactic_left(state)
            elif cmd == "right":
                state = tactic_right(state)
            elif cmd == "assumption":
                state = tactic_assumption(state)
            elif cmd == "reflexivity":
                state = tactic_reflexivity(state)
            elif cmd == "exists":
                state = tactic_exists_intro(state, rest)
            elif cmd == "destruct":
                state = tactic_destruct(state, rest)
            elif cmd == "undo":
                s = state.undo()
                if s: state = s; msg = "Undone."
                else: msg = "No history."
            elif cmd == "redo":
                s = state.redo()
                if s: state = s; msg = "Redone."
                else: msg = "No future."
            else:
                msg = f"Unknown command: {cmd}"
            
            if state and state.is_complete(): msg += "\n✅ Proof complete!"
    except Exception as e:
        msg = f"Error: {str(e)}"
        logger.error(f"Cmd error: {e}")
    return state, msg