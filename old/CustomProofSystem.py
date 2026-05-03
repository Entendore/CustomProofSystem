import re
import os
import sys
from typing import List, Tuple, Optional, Dict, Any, Union, Callable
from dataclasses import dataclass
from copy import deepcopy

# === AST Definitions ===

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

# === Term/Prop Constructors ===

def fun(name: str, args: List[Term]) -> Term:
    return ("fun", name, args)

def var(name: str) -> Term:
    return ("var", name)

def const(name: str) -> Term:
    return ("const", name)

def pred(name: str, args: List[Term]) -> Prop:
    return ("pred", name, args)

def implies(p: Prop, q: Prop) -> Prop:
    return ("implies", p, q)

def and_(p: Prop, q: Prop) -> Prop:
    return ("and", p, q)

def or_(p: Prop, q: Prop) -> Prop:
    return ("or", p, q)

def not_(p: Prop) -> Prop:
    return ("not", p)

def forall(varname: str, body: Prop) -> Prop:
    return ("forall", varname, body)

def exists(varname: str, body: Prop) -> Prop:
    return ("exists", varname, body)

def bottom() -> Prop:
    return ("bottom",)

def eq(t1: Term, t2: Term) -> Prop:
    return pred("=", [t1, t2])

def iff(p: Prop, q: Prop) -> Prop:
    return and_(implies(p, q), implies(q, p))

# === Pretty Printing ===

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
            if name == "=" and len(args) == 2:
                return f"{term_repr(args[0])} = {term_repr(args[1])}"
            return f"{name}({', '.join(term_repr(a) for a in args)})"
        case ('var', x): return x
        case ('const', c): return c
        case _: return str(f)

def prop_repr_paren(f: Prop) -> str:
    if isinstance(f, tuple) and f[0] in {"and", "or", "implies"}:
        return f"({prop_repr(f)})"
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
    if not ctx:
        return "  Context: ∅"
    maxlen = max(len(name) for name, _ in ctx)
    lines = [f"  {name.ljust(maxlen)} : {prop_repr(formula)}" for name, formula in ctx]
    return "  Context:\n" + "\n".join(lines)

def pretty_goal(ctx: Context, goal: Prop) -> str:
    return f"{pretty_context(ctx)}\n  Goal: {prop_repr(goal)}"

# === Substitution and Free Variables ===

def fresh_var(existing: set[str]) -> str:
    base = "x"
    i = 0
    while f"{base}{i}" in existing:
        i += 1
    return f"{base}{i}"

def free_vars(prop: Prop) -> set[str]:
    match prop:
        case ('var', x): return {x}
        case ('const', _): return set()
        case ('pred', _, args): return set().union(*(free_vars_term(a) for a in args))
        case ('not', p): return free_vars(p)
        case ('and' | 'or' | 'implies', p, q): return free_vars(p) | free_vars(q)
        case ('forall' | 'exists', v, body): return free_vars(body) - {v}
        case ('bottom',): return set()
        case _: return set()

def free_vars_term(t: Term) -> set[str]:
    match t:
        case ('var', x): return {x}
        case ('const', _): return set()
        case ('fun', _, args): return set().union(*(free_vars_term(a) for a in args))
        case ('lambda', params, body): return free_vars_term(body) - set(params)
        case ('app', f, a): return free_vars_term(f) | free_vars_term(a)

def substitute_var(prop: Prop, old: str, new: str) -> Prop:
    match prop:
        case ('var', x): return ('var', new) if x == old else prop
        case ('const', _): return prop
        case ('pred', name, args):
            return ('pred', name, [subst_term_var(a, old, new) for a in args])
        case ('not', p): return ('not', substitute_var(p, old, new))
        case ('and' | 'or' | 'implies' as tag, p, q):
            return (tag, substitute_var(p, old, new), substitute_var(q, old, new))
        case ('forall' | 'exists' as tag, v, body):
            if v == old:
                return (tag, v, body)
            elif v == new:
                fresh = fresh_var(free_vars(prop) | {new})
                renamed_body = substitute_var(body, v, fresh)
                return (tag, fresh, substitute_var(renamed_body, old, new))
            else:
                return (tag, v, substitute_var(body, old, new))
        case ('bottom',): return prop
        case _: return prop

def subst_term_var(t: Term, old: str, new: str) -> Term:
    match t:
        case ('var', x): return ('var', new) if x == old else t
        case ('const', _): return t
        case ('fun', f, args): return ('fun', f, [subst_term_var(a, old, new) for a in args])
        case ('lambda', params, body):
            if old in params:
                return t
            elif new in params:
                fresh_params = [fresh_var(set(params)) if p == new else p for p in params]
                body = substitute_var(body, new, fresh_params[params.index(new)])
                return ('lambda', fresh_params, subst_term_var(body, old, new))
            else:
                return ('lambda', params, subst_term_var(body, old, new))
        case ('app', f, a):
            return ('app', subst_term_var(f, old, new), subst_term_var(a, old, new))

def subst_term(t: Term, varname: str, replacement: Term) -> Term:
    match t:
        case ('var', x): return replacement if x == varname else t
        case ('const', _): return t
        case ('fun', name, args):
            return ('fun', name, [subst_term(a, varname, replacement) for a in args])
        case ('lambda', params, body):
            if varname in params:
                return t
            elif any(p in free_vars_term(replacement) for p in params):
                fresh_params = [fresh_var(free_vars_term(body) | free_vars_term(replacement)) for _ in params]
                renamed_body = body
                for old, new in zip(params, fresh_params):
                    renamed_body = subst_term_var(renamed_body, old, new)
                return ('lambda', fresh_params, subst_term(renamed_body, varname, replacement))
            else:
                return ('lambda', params, subst_term(body, varname, replacement))
        case ('app', f, a):
            return ('app', subst_term(f, varname, replacement), subst_term(a, varname, replacement))

def substitute(prop: Prop, varname: str, term: Term) -> Prop:
    match prop:
        case ('var', x): return prop
        case ('const', _): return prop
        case ('pred', name, args):
            return ('pred', name, [subst_term(a, varname, term) for a in args])
        case ('not', p): return ('not', substitute(p, varname, term))
        case ('and' | 'or' | 'implies' as tag, p, q):
            return (tag, substitute(p, varname, term), substitute(q, varname, term))
        case ('forall' | 'exists' as tag, v, body):
            if v == varname:
                return (tag, v, body)
            elif v in free_vars_term(term):
                fresh = fresh_var(free_vars(body) | free_vars_term(term))
                renamed = substitute_var(body, v, fresh)
                return (tag, fresh, substitute(renamed, varname, term))
            else:
                return (tag, v, substitute(body, varname, term))
        case ('bottom',): return prop
        case _: return prop

def beta_reduce(term: Term) -> Term:
    match term:
        case ("app", ("lambda", [x], body), arg):
            return beta_reduce(subst_term(body, x, arg))
        case ("app", f, a):
            f_red = beta_reduce(f)
            a_red = beta_reduce(a)
            if f_red != f or a_red != a:
                return beta_reduce(("app", f_red, a_red))
            return ("app", f_red, a_red)
        case ("lambda", params, body):
            body_red = beta_reduce(body)
            if body_red != body:
                return ("lambda", params, body_red)
            return term
        case ("fun", name, args):
            new_args = [beta_reduce(arg) for arg in args]
            if new_args != args:
                return ("fun", name, new_args)
            return term
        case _:
            return term

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
        case _:
            return p1 == p2

# === Proof State and Proof Recording ===

@dataclass
class ProofStep:
    tactic_name: str
    arguments: List[Any]
    subgoals_before: List[Goal]
    subgoals_after: List[Goal]

class ProofTree:
    def __init__(self):
        self.steps = []
    
    def record_step(self, tactic_name: str, arguments: List[Any], state_before: 'ProofState', state_after: 'ProofState'):
        step = ProofStep(tactic_name, arguments, state_before.goals, state_after.goals)
        self.steps.append(step)
    
    def pretty_print(self):
        if not self.steps:
            print("No proof steps recorded")
            return
        
        print("Proof steps:")
        for i, step in enumerate(self.steps):
            print(f"{i+1}. {step.tactic_name} {step.arguments}")
            print(f"   Goals: {len(step.subgoals_before)} → {len(step.subgoals_after)}")
    
    def export_coq(self, theorem_name: str) -> str:
        if not self.steps:
            return ""
        
        initial_goal = self.steps[0].subgoals_before[0]
        ctx, goal = initial_goal
        
        coq_lines = [f"Theorem {theorem_name} : {prop_to_coq(goal)}.", "Proof."]
        
        for step in self.steps:
            coq_cmd = tactic_to_coq(step.tactic_name, step.arguments)
            if coq_cmd:
                coq_lines.append(f"  {coq_cmd}.")
        
        coq_lines.append("Qed.")
        return "\n".join(coq_lines)

class ProofState:
    def __init__(self, goals: List[Goal], proof_tree: Optional[ProofTree] = None):
        self.goals = goals
        self.proof_tree = proof_tree or ProofTree()
    
    def current(self) -> Optional[Goal]:
        return self.goals[-1] if self.goals else None

    def is_complete(self) -> bool:
        return not self.goals

    def add_subgoals(self, new_goals: List[Goal]) -> 'ProofState':
        return ProofState(self.goals[:-1] + new_goals, self.proof_tree)

    def __str__(self):
        if self.is_complete():
            return "✅ Proof complete."
        
        lines = []
        for i, (ctx, goal) in enumerate(self.goals):
            lines.append(f"{'>>> ' if i == len(self.goals) - 1 else '    '}Goal {i+1}:")
            lines.append(pretty_goal(ctx, goal))
            lines.append("")
        return "\n".join(lines)

# === Tactics ===

def recorded_tactic(original_tactic):
    def wrapper(state: ProofState, *args, **kwargs) -> ProofState:
        state_before = ProofState(state.goals.copy(), state.proof_tree)
        result = original_tactic(state, *args, **kwargs)
        state.proof_tree.record_step(original_tactic.__name__, list(args), state_before, result)
        return result
    return wrapper

@recorded_tactic
def tactic_intro(state: ProofState, name: str = "H") -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    tag = goal[0]
    if tag == "implies":
        premise, conclusion = goal[1], goal[2]
        new_ctx = ctx + [(name, premise)]
        return state.add_subgoals([(new_ctx, conclusion)])
    elif tag == "forall":
        varname, body = goal[1], goal[2]
        fresh_var_term = var(name)
        new_body = substitute(body, varname, fresh_var_term)
        return state.add_subgoals([(ctx, new_body)])
    else:
        raise Exception("intro tactic failed: goal is not implication or forall")

@recorded_tactic
def tactic_exact(state: ProofState, term: Union[str, Prop]) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current

    if isinstance(term, str):
        hyp = next((f for n, f in ctx if n == term), None)
        if hyp and alpha_eq(hyp, goal):
            return ProofState(state.goals[:-1], state.proof_tree)
        else:
            raise Exception("exact tactic failed: term doesn't match goal or not in context")
    else:
        if alpha_eq(term, goal):
            return ProofState(state.goals[:-1], state.proof_tree)
        else:
            raise Exception("exact tactic failed: formula doesn't match goal")

@recorded_tactic
def tactic_split(state: ProofState) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    if goal[0] == "and":
        left, right = goal[1], goal[2]
        return state.add_subgoals([(ctx, left), (ctx, right)])
    else:
        raise Exception("split tactic failed: goal is not conjunction")

@recorded_tactic
def tactic_destruct(state: ProofState, name: str) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    for i, (n, f) in enumerate(ctx):
        if n == name:
            hyp = f
            ctx_before = ctx[:i]
            ctx_after = ctx[i+1:]
            if hyp[0] == "and":
                new_ctx = ctx_before + [(f"{name}_left", hyp[1]), (f"{name}_right", hyp[2])] + ctx_after
                return state.add_subgoals([(new_ctx, goal)])
            elif hyp[0] == "or":
                left_ctx = ctx_before + [(f"{name}_left", hyp[1])] + ctx_after
                right_ctx = ctx_before + [(f"{name}_right", hyp[2])] + ctx_after
                return state.add_subgoals([(left_ctx, goal), (right_ctx, goal)])
            else:
                raise Exception("destruct tactic failed: hypothesis is not ∧ or ∨")
    raise Exception("destruct tactic failed: name not found")

@recorded_tactic
def tactic_left(state: ProofState) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    if goal[0] == "or":
        return state.add_subgoals([(ctx, goal[1])])
    else:
        raise Exception("left tactic failed: goal is not disjunction")

@recorded_tactic
def tactic_right(state: ProofState) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    if goal[0] == "or":
        return state.add_subgoals([(ctx, goal[2])])
    else:
        raise Exception("right tactic failed: goal is not disjunction")

@recorded_tactic
def tactic_forall_elim(state: ProofState, hyp_idx: int, term: Term) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    if hyp_idx < 0 or hyp_idx >= len(ctx):
        raise Exception("forall_elim failed: hypothesis index out of range")
    hyp_name, hyp = ctx[hyp_idx]
    if hyp[0] != "forall":
        raise Exception("forall_elim failed: hypothesis at index is not ∀")
    varname, body = hyp[1], hyp[2]
    new_prop = substitute(body, varname, term)
    new_ctx = ctx + [(f"{hyp_name}_inst", new_prop)]
    return state.add_subgoals([(new_ctx, goal)])

@recorded_tactic
def tactic_exists_intro(state: ProofState, term: Term) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    if goal[0] == "exists":
        varname, body = goal[1], goal[2]
        new_goal = substitute(body, varname, term)
        return state.add_subgoals([(ctx, new_goal)])
    else:
        raise Exception("exists_intro failed: goal is not ∃")

@recorded_tactic
def tactic_contradiction(state: ProofState) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, _ = current
    if any(hyp[1][0] == "bottom" for hyp in ctx):
        return ProofState(state.goals[:-1], state.proof_tree)
    else:
        raise Exception("contradiction failed: ⊥ not in context")

@recorded_tactic
def tactic_assume(state: ProofState, prop: Prop) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current

    existing_names = {name for name, _ in ctx}
    n = 1
    while True:
        name = f"H{n}"
        if name not in existing_names:
            break
        n += 1

    new_ctx = ctx + [(name, prop)]
    return state.add_subgoals([(new_ctx, goal)])

@recorded_tactic
def tactic_rename(state: ProofState, old_name: str, new_name: str) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current

    names = [name for name, _ in ctx]
    if old_name not in names:
        raise Exception(f"rename failed: hypothesis '{old_name}' not found")
    if new_name in names:
        raise Exception(f"rename failed: hypothesis '{new_name}' already exists")

    new_ctx = [(new_name if name == old_name else name, prop) for name, prop in ctx]
    return state.add_subgoals([(new_ctx, goal)])

@recorded_tactic
def tactic_clear(state: ProofState, name: str) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current

    new_ctx = [(n, p) for (n, p) in ctx if n != name]
    if len(new_ctx) == len(ctx):
        raise Exception(f"clear failed: hypothesis '{name}' not found")

    return state.add_subgoals([(new_ctx, goal)])

@recorded_tactic
def tactic_not_intro(state: ProofState, name: str = "H") -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    if goal[0] != "not":
        raise Exception("not_intro tactic failed: goal is not a negation ¬P")
    p = goal[1]
    new_ctx = ctx + [(name, p)]
    return state.add_subgoals([(new_ctx, bottom())])

@recorded_tactic
def tactic_not_elim(state: ProofState, hyp_name: str) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current

    hyp = next((f for n, f in ctx if n == hyp_name), None)
    if hyp is None:
        raise Exception(f"not_elim failed: hypothesis '{hyp_name}' not found")

    if hyp[0] == 'not' and hyp[1][0] == 'not':
        P = hyp[1][1]
        if alpha_eq(P, goal):
            return ProofState(state.goals[:-1], state.proof_tree)
        else:
            raise Exception("not_elim failed: goal doesn't match ¬¬P inner proposition")
    else:
        raise Exception("not_elim failed: hypothesis is not double negation")

@recorded_tactic
def tactic_assumption(state: ProofState) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    for name, hyp in reversed(ctx):
        if alpha_eq(hyp, goal):
            return ProofState(state.goals[:-1], state.proof_tree)
    raise Exception("assumption tactic failed: no matching hypothesis")

@recorded_tactic
def tactic_reflexivity(state: ProofState) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    if goal[0] == "pred" and goal[1] == "=":
        left, right = goal[2]
        if term_eq(left, right):
            return ProofState(state.goals[:-1], state.proof_tree)
    raise Exception("reflexivity failed: goal is not t = t")

@recorded_tactic
def tactic_auto(state: ProofState, depth: int = 3) -> ProofState:
    if depth <= 0:
        raise Exception("Auto depth exceeded")
    
    try:
        return tactic_assumption(state)
    except:
        pass
    
    try:
        return tactic_contradiction(state)
    except:
        pass
    
    current = state.current()
    if current:
        ctx, goal = current
        match goal:
            case ('and', p, q):
                try:
                    return tactic_split(state)
                except:
                    pass
            case ('implies', p, q):
                try:
                    new_state = tactic_intro(state, f"H_auto{depth}")
                    return tactic_auto(new_state, depth - 1)
                except:
                    pass
            case ('forall', v, body):
                try:
                    new_state = tactic_intro(state, f"x_auto{depth}")
                    return tactic_auto(new_state, depth - 1)
                except:
                    pass
    
    for i, (name, hyp) in enumerate(ctx):
        match hyp:
            case ('implies', A, B) if alpha_eq(B, goal):
                try:
                    subgoal_state = ProofState([(ctx, A)], state.proof_tree)
                    proved_subgoal = tactic_auto(subgoal_state, depth - 1)
                    if proved_subgoal.is_complete():
                        return tactic_exact(state, name)
                except:
                    continue
    
    raise Exception("Auto tactic failed")

@recorded_tactic
def tactic_dne(state: ProofState, hyp_name: str) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current

    for name, prop in ctx:
        if name == hyp_name and prop[0] == "not" and prop[1][0] == "not":
            inner = prop[1][1]
            if alpha_eq(inner, goal):
                return ProofState(state.goals[:-1], state.proof_tree)
    raise Exception("dne tactic failed: hypothesis ¬¬P not found")

# === Lexer and Parser ===

token_specification = [
    ('FORALL',   r'∀|forall'),
    ('EXISTS',   r'∃|exists'),
    ('NOT',      r'¬|~|not'),
    ('BOTTOM',   r'⊥|bottom'),
    ('AND',      r'∧|&|and'),
    ('OR',       r'∨|\||or'),
    ('IMPLIES',  r'→|->|implies'),
    ('IFF',      r'↔|<=>|iff'),
    ('EQ',       r'='),
    ('DOT',      r'\.'),
    ('LPAREN',   r'\('),
    ('RPAREN',   r'\)'),
    ('COMMA',    r','),
    ('LAMBDA',   r'λ|lambda'),
    ('VAR',      r'[a-z][a-zA-Z0-9_]*'),
    ('CONST',    r'[A-Z][a-zA-Z0-9_]*'),
    ('SKIP',     r'[ \t\n]+'),
    ('MISMATCH', r'.'),
]

token_re = re.compile('|'.join(f'(?P<{name}>{pattern})' for name, pattern in token_specification))

def lex(characters: str) -> List[Tuple[str, str, int, int]]:
    tokens = []
    line_start = 0
    for mo in token_re.finditer(characters):
        kind = mo.lastgroup
        value = mo.group()
        start = mo.start()
        end = mo.end()
        if kind == 'SKIP':
            continue
        elif kind == 'MISMATCH':
            raise SyntaxError(f'Unexpected character {value!r} at position {start}')
        else:
            tokens.append((kind, value, start, end))
    return tokens

class Parser:
    def __init__(self, tokens: List[Tuple[str, str]]):
        self.tokens = tokens
        self.pos = 0

    def peek(self) -> Optional[Tuple[str, str]]:
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def consume(self, expected_type=None) -> Tuple[str, str]:
        token = self.peek()
        if token is None:
            raise SyntaxError("Unexpected end of input")
        if expected_type and token[0] != expected_type:
            raise SyntaxError(f"Expected {expected_type}, got {token[0]}")
        self.pos += 1
        return token

    def parse(self) -> Prop:
        result = self.parse_implication()
        if self.peek() is not None:
            raise SyntaxError("Unexpected token after end of expression")
        return result

    def parse_implication(self) -> Prop:
        left = self.parse_iff()
        while self.peek() and self.peek()[0] == 'IMPLIES':
            self.consume('IMPLIES')
            right = self.parse_implication()
            left = implies(left, right)
        return left

    def parse_iff(self) -> Prop:
        left = self.parse_or()
        while self.peek() and self.peek()[0] == 'IFF':
            self.consume('IFF')
            right = self.parse_or()
            left = iff(left, right)
        return left

    def parse_or(self) -> Prop:
        left = self.parse_and()
        while self.peek() and self.peek()[0] == 'OR':
            self.consume('OR')
            right = self.parse_and()
            left = or_(left, right)
        return left

    def parse_and(self) -> Prop:
        left = self.parse_not()
        while self.peek() and self.peek()[0] == 'AND':
            self.consume('AND')
            right = self.parse_not()
            left = and_(left, right)
        return left

    def parse_not(self) -> Prop:
        if self.peek() and self.peek()[0] == 'NOT':
            self.consume('NOT')
            prop = self.parse_not()
            return not_(prop)
        else:
            return self.parse_quantifier_or_atomic()

    def parse_quantifier_or_atomic(self) -> Prop:
        tok = self.peek()
        if tok and tok[0] == 'FORALL':
            self.consume('FORALL')
            var_token = self.consume('VAR')
            self.consume('DOT')
            body = self.parse_implication()
            return forall(var_token[1], body)
        elif tok and tok[0] == 'EXISTS':
            self.consume('EXISTS')
            var_token = self.consume('VAR')
            self.consume('DOT')
            body = self.parse_implication()
            return exists(var_token[1], body)
        else:
            return self.parse_atomic()

    def parse_atomic(self) -> Prop:
        tok = self.peek()
        if tok is None:
            raise SyntaxError("Unexpected end of input")

        if tok[0] == 'LPAREN':
            self.consume('LPAREN')
            prop = self.parse_implication()
            self.consume('RPAREN')
            return prop
        
        elif tok[0] == 'CONST':
            pred_name = self.consume('CONST')[1]
            if self.peek() and self.peek()[0] == 'LPAREN':
                self.consume('LPAREN')
                args = self.parse_term_list()
                self.consume('RPAREN')
                return pred(pred_name, args)
            else:
                return pred(pred_name, [])
            
        elif tok[0] == 'VAR':
            var_name = self.consume('VAR')[1]
            return var(var_name)
        
        elif tok[0] == 'BOTTOM':
            self.consume('BOTTOM')
            return bottom()

        elif tok[0] == 'EQ':
            self.consume('EQ')
            left = self.parse_term()
            if self.peek() and self.peek()[0] == 'EQ':
                self.consume('EQ')
                right = self.parse_term()
                return eq(left, right)
            else:
                raise SyntaxError("Expected second term for equality")

        else:
            raise SyntaxError(f"Unexpected token {tok}")

    def parse_term_list(self) -> List[Term]:
        terms = [self.parse_term()]
        while self.peek() and self.peek()[0] == 'COMMA':
            self.consume('COMMA')
            terms.append(self.parse_term())
        return terms
    
    def parse_term(self) -> Term:
        tok = self.peek()
        if tok is None:
            raise SyntaxError("Unexpected end of input in term")
        if tok[0] == 'VAR':
            return var(self.consume('VAR')[1])
        elif tok[0] == 'CONST':
            name = self.consume('CONST')[1]
            if self.peek() and self.peek()[0] == 'LPAREN':
                self.consume('LPAREN')
                args = self.parse_term_list()
                self.consume('RPAREN')
                return fun(name, args)
            else:
                return const(name)
        elif tok[0] == 'LAMBDA':
            self.consume('LAMBDA')
            params = []
            while self.peek() and self.peek()[0] == 'VAR':
                params.append(self.consume('VAR')[1])
            self.consume('DOT')
            body = self.parse_term()
            return ("lambda", params, body)
        elif tok[0] == 'LPAREN':
            self.consume('LPAREN')
            term = self.parse_term()
            self.consume('RPAREN')
            return term
        else:
            raise SyntaxError(f"Unexpected token in term: {tok}")

def parse_formula(formula_str: str) -> Prop:
    tokens = lex(formula_str)
    parser = Parser(tokens)
    return parser.parse()

def parse_term(term_str: str) -> Term:
    tokens = lex(term_str)
    parser = Parser(tokens)
    return parser.parse_term()

# === Coq Export ===

def prop_to_coq(prop: Prop) -> str:
    match prop:
        case ('not', p): return f"~({prop_to_coq(p)})"
        case ('and', p, q): return f"({prop_to_coq(p)} /\\ {prop_to_coq(q)})"
        case ('or', p, q): return f"({prop_to_coq(p)} \\/ {prop_to_coq(q)})"
        case ('implies', p, q): return f"({prop_to_coq(p)} -> {prop_to_coq(q)})"
        case ('forall', v, body): return f"(forall {v}, {prop_to_coq(body)})"
        case ('exists', v, body): return f"(exists {v}, {prop_to_coq(body)})"
        case ('bottom',): return "False"
        case ('pred', name, args):
            if name == "=" and len(args) == 2:
                return f"({term_to_coq(args[0])} = {term_to_coq(args[1])})"
            return f"{name}({', '.join(term_to_coq(a) for a in args)})"
        case ('var', x): return x
        case ('const', c): return c
        case _: return str(prop)

def term_to_coq(t: Term) -> str:
    match t:
        case ("var", x): return x
        case ("const", c): return c
        case ("fun", name, args): return f"{name}({', '.join(term_to_coq(a) for a in args)})"
        case ("lambda", params, body): return f"(fun {', '.join(params)} => {term_to_coq(body)})"
        case ("app", f, a): return f"({term_to_coq(f)} {term_to_coq(a)})"
        case _: return str(t)

def tactic_to_coq(tactic_name: str, arguments: List[Any]) -> str:
    mapping = {
        "intro": "intros",
        "exact": "exact",
        "split": "split",
        "left": "left",
        "right": "right",
        "destruct": "destruct",
        "contradiction": "contradiction",
        "assumption": "assumption",
        "reflexivity": "reflexivity",
        "exists_intro": "exists",
    }
    
    base = mapping.get(tactic_name, tactic_name)
    if arguments:
        args_str = " ".join(str(arg) for arg in arguments)
        return f"{base} {args_str}"
    return base

# === Command Processing ===

def explain_tactic(tactic_name: str) -> str:
    explanations = {
        "intro": "Introduces an implication or universal quantifier. For A → B, it assumes A and proves B. For ∀x. P(x), it introduces a fresh variable.",
        "exact": "Solves the goal when it exactly matches a hypothesis.",
        "split": "Splits a conjunction goal A ∧ B into two subgoals: prove A and prove B.",
        "destruct": "Performs case analysis on a disjunction or conjunction hypothesis.",
        "left": "Solves a disjunction goal A ∨ B by proving A.",
        "right": "Solves a disjunction goal A ∨ B by proving B.",
        "forall_elim": "Instantiates a universal quantifier with a specific term.",
        "exists_intro": "Provides a witness for an existential quantifier.",
        "contradiction": "Solves the goal when ⊥ is in the context.",
        "assume": "Adds a new hypothesis to the context.",
        "rename": "Renames a hypothesis.",
        "clear": "Removes a hypothesis from the context.",
        "not_intro": "Proves ¬P by assuming P and proving ⊥.",
        "not_elim": "Uses double negation ¬¬P to prove P.",
        "assumption": "Solves the goal if it matches a hypothesis.",
        "reflexivity": "Solves equality goals of the form t = t.",
        "auto": "Attempts to automatically prove the goal using simple tactics.",
        "dne": "Double negation elimination: uses ¬¬P to prove P.",
    }
    return explanations.get(tactic_name, "No explanation available.")

def tactic_hint(state: ProofState) -> ProofState:
    current = state.current()
    if current is None:
        print("No current goal")
        return state
    
    ctx, goal = current
    print(f"Goal: {prop_repr(goal)}")
    print("Possible next steps:")
    
    match goal:
        case ('implies', p, q):
            print("- Use 'intro' to assume the premise")
            print("- Look for hypotheses that might help prove the conclusion")
        case ('and', p, q):
            print("- Use 'split' to break into two subgoals")
        case ('forall', v, body):
            print("- Use 'intro' to introduce a new variable")
        case ('exists', v, body):
            print("- Use 'exists_intro <term>' to provide a witness")
        case ('or', p, q):
            print("- Use 'left' to prove the left disjunct")
            print("- Use 'right' to prove the right disjunct")
        case ('not', p):
            print("- Use 'not_intro' to assume the negation and prove ⊥")
        case ('pred', "=", [left, right]) if term_eq(left, right):
            print("- Use 'reflexivity' to solve the equality")
        case _:
            print("- Try 'assumption' if goal matches a hypothesis")
            print("- Try 'auto' for automatic proof search")
    
    for name, hyp in ctx:
        match hyp:
            case ('implies', A, B) if alpha_eq(B, goal):
                print(f"- Use 'exact {name}' or prove {prop_repr(A)} first")
            case ('and', A, B):
                print(f"- Use 'destruct {name}' to break the hypothesis apart")
            case ('or', A, B):
                print(f"- Use 'destruct {name}' for case analysis")
            case ('not', ('not', P)) if alpha_eq(P, goal):
                print(f"- Use 'dne {name}' for double negation elimination")
            case ('forall', v, body):
                print(f"- Use 'forall_elim {ctx.index((name, hyp))} <term>' to instantiate")
    
    return state

def process_command(state: Optional[ProofState], command: str) -> Optional[ProofState]:
    cmd = command.strip()
    if not cmd:
        return state
    
    parts = cmd.split(maxsplit=1)
    cmd_name = parts[0]
    arg = parts[1] if len(parts) > 1 else None

    try:
        if cmd_name == "help":
            print_help()
            return state
        elif cmd_name == "goal":
            if arg is None:
                print("Usage: goal <expr>")
                return state
            prop = parse_formula(arg)
            new_state = ProofState([([], prop)])
            print(f"Goal set: {prop_repr(prop)}")
            return new_state

        if state is None:
            print("No active proof. Use 'goal <expr>' to set a goal.")
            return None

        if cmd_name == "intro":
            name = arg if arg else "H"
            return tactic_intro(state, name)

        elif cmd_name == "exact":
            if arg is None:
                print("Usage: exact <hyp_name> or exact <formula>")
                return state
            try:
                # Try parsing as formula first
                prop = parse_formula(arg)
                return tactic_exact(state, prop)
            except:
                # Treat as hypothesis name
                return tactic_exact(state, arg)

        elif cmd_name == "split":
            return tactic_split(state)

        elif cmd_name == "destruct":
            if arg is None:
                print("Usage: destruct <hyp_name>")
                return state
            return tactic_destruct(state, arg)

        elif cmd_name == "left":
            return tactic_left(state)

        elif cmd_name == "right":
            return tactic_right(state)

        elif cmd_name == "forall_elim":
            if arg is None:
                print("Usage: forall_elim <hyp_name> <term>")
                return state
            parts2 = arg.split(maxsplit=1)
            if len(parts2) != 2:
                print("Usage: forall_elim <hyp_name> <term>")
                return state
            hyp_name, term_str = parts2
            term = parse_term(term_str)
            current = state.current()
            if current:
                ctx, _ = current
                hyp_idx = next(i for i, (name, _) in enumerate(ctx) if name == hyp_name)
                return tactic_forall_elim(state, hyp_idx, term)

        elif cmd_name == "exists_intro":
            if arg is None:
                print("Usage: exists_intro <term>")
                return state
            term = parse_term(arg)
            return tactic_exists_intro(state, term)

        elif cmd_name == "contradiction":
            return tactic_contradiction(state)

        elif cmd_name == "assume":
            if arg is None:
                print("Usage: assume <formula>")
                return state
            prop = parse_formula(arg)
            return tactic_assume(state, prop)

        elif cmd_name == "rename":
            if arg is None:
                print("Usage: rename <old_name> <new_name>")
                return state
            parts2 = arg.split()
            if len(parts2) != 2:
                print("Usage: rename <old_name> <new_name>")
                return state
            old_name, new_name = parts2
            return tactic_rename(state, old_name, new_name)

        elif cmd_name == "clear":
            if arg is None:
                print("Usage: clear <hyp_name>")
                return state
            return tactic_clear(state, arg)

        elif cmd_name == "not_intro":
            name = arg if arg else "H"
            return tactic_not_intro(state, name)

        elif cmd_name == "not_elim":
            if arg is None:
                print("Usage: not_elim <hyp_name>")
                return state
            return tactic_not_elim(state, arg)

        elif cmd_name == "assumption":
            return tactic_assumption(state)

        elif cmd_name == "reflexivity":
            return tactic_reflexivity(state)

        elif cmd_name == "auto":
            depth = int(arg) if arg and arg.isdigit() else 3
            return tactic_auto(state, depth)

        elif cmd_name == "dne":
            if arg is None:
                print("Usage: dne <hyp_name>")
                return state
            return tactic_dne(state, arg)

        elif cmd_name == "hint":
            return tactic_hint(state)

        elif cmd_name == "state":
            print(state)
            return state

        elif cmd_name == "context":
            current = state.current()
            if current is None:
                print("No current goal")
                return state
            ctx, _ = current
            if not ctx:
                print("Context is empty")
            else:
                for i, (name, prop) in enumerate(ctx):
                    print(f"{i}: {name} : {prop_repr(prop)}")
            return state

        elif cmd_name == "explain":
            if arg is None:
                print("Usage: explain <tactic_name>")
                return state
            print(explain_tactic(arg))
            return state

        elif cmd_name == "export":
            if arg is None:
                print("Usage: export <theorem_name>")
                return state
            coq_code = state.proof_tree.export_coq(arg)
            print("Coq export:")
            print(coq_code)
            return state

        elif cmd_name == "proof":
            state.proof_tree.pretty_print()
            return state

        elif cmd_name == "exit":
            print("Exiting.")
            sys.exit(0)

        else:
            print(f"Unknown command: {cmd_name}")
            return state

    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
        return state

def print_help():
    print("""Available commands:
Basic proof commands:
  goal <expr>                   Set current goal
  intro [name]                  Introduce implication/forall
  exact <hyp|formula>           Solve with exact match
  split                         Split conjunction
  destruct <hyp>                Destruct ∧/∨ hypothesis
  left/right                    Solve disjunction
  forall_elim <hyp> <term>      Instantiate ∀
  exists_intro <term>           Provide ∃ witness
  contradiction                 Solve from ⊥
  assume <formula>              Add hypothesis
  rename <old> <new>            Rename hypothesis
  clear <hyp>                   Remove hypothesis
  not_intro [name]              Prove ¬P by assuming P
  not_elim <hyp>                Use ¬¬P to prove P
  assumption                    Solve if goal matches hypothesis
  reflexivity                   Solve t = t
  auto [depth]                  Automatic proof search
  dne <hyp>                     Double negation elimination

Information commands:
  state                         Show current proof state
  context                       Show context with indices
  hint                          Get proof hints
  explain <tactic>              Explain a tactic
  proof                         Show proof steps
  export <name>                 Export to Coq

Other commands:
  help                          Show this help
  exit                          Quit
""")

# === REPL and Main ===

def repl():
    print("🔍 Advanced Proof Assistant")
    print("Type 'help' for commands, 'exit' to quit.")
    state: Optional[ProofState] = None
    history: List[str] = []
    
    while True:
        try:
            cmd = input("proof> ")
            history.append(cmd)
            
            if cmd == "undo":
                if len(history) > 1 and state:
                    print("Undo not fully implemented - use 'goal' to restart")
                continue
                
            elif cmd == "history":
                for i, hist_cmd in enumerate(history[-10:]):
                    print(f"{i+1}: {hist_cmd}")
                continue
            
            old_state = state
            state = process_command(state, cmd)
            
            if state and state != old_state:
                if state.is_complete():
                    print("✅ Proof complete!")
                    print("Proof summary:")
                    state.proof_tree.pretty_print()
                    print("\nUse 'export <name>' to export to Coq")
                else:
                    print(f"Remaining goals: {len(state.goals)}")
                    
        except EOFError:
            print("\nExiting.")
            break
        except KeyboardInterrupt:
            print("\nUse 'exit' to quit or continue proof")
        except Exception as e:
            print(f"Unexpected error: {e}")
            import traceback
            traceback.print_exc()

def run_proof_file(filename: str, step_by_step: bool = False):
    print(f"Running proof script: {filename}")
    state: Optional[ProofState] = None
    with open(filename, 'r', encoding='utf-8') as f:
        for lineno, line in enumerate(f, 1):
            cmd = line.strip()
            if not cmd or cmd.startswith('#'):
                continue
            print(f">>> {cmd}")
            state = process_command(state, cmd)
            if state and state.is_complete():
                print("Proof complete!")
                break
            if step_by_step:
                input("Press Enter to continue...")
    print("----- End of proof script -----\n")
    if state and not state.is_complete():
        print("Warning: Proof not completed!")

def run_proofs_in_folder(folder_path: str):
    if not os.path.isdir(folder_path):
        print(f"Not a directory: {folder_path}")
        return
    proof_files = [f for f in os.listdir(folder_path) if f.endswith(('.txt', '.proof'))]
    if not proof_files:
        print(f"No proof files found in {folder_path}")
        return
    for proof_file in sorted(proof_files):
        full_path = os.path.join(folder_path, proof_file)
        print(f"\n=== Running {proof_file} ===")
        run_proof_file(full_path)

def main():
    if len(sys.argv) == 1:
        repl()
    elif len(sys.argv) == 2:
        path = sys.argv[1]
        if os.path.isdir(path):
            run_proofs_in_folder(path)
        elif os.path.isfile(path):
            run_proof_file(path)
        else:
            print(f"Invalid path: {path}")
    elif len(sys.argv) == 3 and sys.argv[1] == "--step":
        run_proof_file(sys.argv[2], step_by_step=True)
    else:
        print(f"Usage: {sys.argv[0]} [--step] [prooffile|proofs_folder]")
        sys.exit(1)

if __name__ == "__main__":
    main()