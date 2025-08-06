import re
import os
import sys
from typing import List, Tuple, Optional, Callable, Union

# === AST using plain tuples and dicts ===

# Prop is represented as tuples:
# Examples:
# ("var", "P")
# ("const", "A")
# ("pred", "P", [terms])
# ("implies", premise, conclusion)
# ("and", left, right)
# ("or", left, right)
# ("not", prop)
# ("forall", var_name, body)
# ("exists", var_name, body)
# ("bottom",)

Term = Union[Tuple[str, str], Tuple[str, str, List], Tuple[str, str, List['Term']]]  # ("var", name) or ("const", name) or ("pred", name, [args])

Prop = Union[
    Tuple[str, str],  # "var" or "const"
    Tuple[str],       # "bottom"
    Tuple[str, str, List], # "pred"
    Tuple[str, 'Prop', 'Prop'], # "implies", "and", "or"
    Tuple[str, 'Prop'], # "not"
    Tuple[str, str, 'Prop'],  # "forall", "exists"
]

Context = List[Tuple[str, Prop]] 

def fun(name: str, args: List[Term]) -> Term:
    return ("fun", name, args)

def var(name: str) -> Prop:
    return ("var", name)

def const(name: str) -> Prop:
    return ("const", name)

def pred(name: str, args: List[Term]) -> Prop:
    return ("pred", name, args)

def implies(premise: Prop, conclusion: Prop) -> Prop:
    return ("implies", premise, conclusion)

def and_(left: Prop, right: Prop) -> Prop:
    return ("and", left, right)

def or_(left: Prop, right: Prop) -> Prop:
    return ("or", left, right)

def not_(p: Prop) -> Prop:
    return ("not", p)

def forall(varname: str, body: Prop) -> Prop:
    return ("forall", varname, body)

def exists(varname: str, body: Prop) -> Prop:
    return ("exists", varname, body)

def bottom() -> Prop:
    return ("bottom",)

# === Helpers ===

def prop_eq(p1: Prop, p2: Prop) -> bool:
    return p1 == p2

def prop_repr(f):
    match f:
        case ('not', p): return f"¬{prop_repr_paren(p)}"
        case ('and', p, q): return f"{prop_repr_paren(p)} ∧ {prop_repr_paren(q)}"
        case ('or', p, q): return f"{prop_repr_paren(p)} ∨ {prop_repr_paren(q)}"
        case ('imp', p, q): return f"{prop_repr_paren(p)} → {prop_repr(q)}"
        case ('iff', p, q): return f"{prop_repr_paren(p)} ↔ {prop_repr_paren(q)}"
        case ('forall', var, body): return f"∀{var}. {prop_repr(body)}"
        case ('exists', var, body): return f"∃{var}. {prop_repr(body)}"
        case ('⊥',): return "⊥"
        case str(): return f
        case _: return str(f)


def prop_repr_paren(f):
    if isinstance(f, tuple) and f[0] in {'and', 'or', 'imp', 'iff'}:
        return f"({prop_repr(f)})"
    return prop_repr(f)


def pretty_context(context):
    if not context:
        return "  Context: ∅"
    
    maxlen = max(len(name) for name, _ in context)
    lines = [f"  {name.ljust(maxlen)} : {prop_repr(formula)}" for name, formula in context]
    return "  Context:\n" + "\n".join(lines)


def pretty_goal(context, goal):
    ctx_str = pretty_context(context)
    goal_str = f"  Goal: {prop_repr(goal)}"
    return f"{ctx_str}\n{goal_str}"


def term_repr(t: Term) -> str:
    tag = t[0]
    if tag in ("var", "const"):
        return t[1]
    else:
        return f"<term:{t}>"

# === Substitution ===

def substitute(prop: Prop, varname: str, term: Term) -> Prop:
    tag = prop[0]
    if tag == "var":
        return prop if prop[1] != varname else term
    elif tag == "const":
        return prop
    elif tag == "pred":
        name, args = prop[1], prop[2]
        new_args = [term if (arg[0] == "var" and arg[1] == varname) else arg for arg in args]
        return ("pred", name, new_args)
    elif tag in ("implies", "and", "or"):
        left, right = prop[1], prop[2]
        return (tag, substitute(left, varname, term), substitute(right, varname, term))
    elif tag == "not":
        return ("not", substitute(prop[1], varname, term))
    elif tag == "forall":
        v, body = prop[1], prop[2]
        if v == varname:
            return prop
        return ("forall", v, substitute(body, varname, term))
    elif tag == "exists":
        v, body = prop[1], prop[2]
        if v == varname:
            return prop
        return ("exists", v, substitute(body, varname, term))
    elif tag == "bottom":
        return prop
    else:
        return prop

# === Proof state ===

# A goal is (context, goal)
Context = List[Prop]
Goal = Tuple[Context, Prop]

class ProofState:
    def __init__(self, goals: List[Goal]):
        self.goals = goals 
        self.context = []

    def current(self) -> Optional[Goal]:
        return self.goals[-1] if self.goals else None

    def is_complete(self) -> bool:
        return len(self.goals) == 0

    def add_subgoals(self, new_goals: List[Goal]) -> 'ProofState':
        return ProofState(self.goals[:-1] + new_goals)

    def pretty_print_proofstate(self):
        if self.is_complete():
            return "Proof complete."

        lines = []
        for i, (ctx, goal) in enumerate(self.goals):
            lines.append(f"Goal {i+1}:")
            if not ctx:
                lines.append("  Context: ∅")
            else:
                lines.append("  Context:")
                max_name_len = max(len(name) for name, _ in ctx)
                for name, prop in ctx:
                    lines.append(f"    {name.ljust(max_name_len)} : {prop_repr(prop)}")
            lines.append(f"  Goal: {prop_repr(goal)}")
            lines.append("")
        return "\n".join(lines)

ProofState.__repr__ = ProofState.pretty_print_proofstate

# === Tactics ===

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
        fresh_var = ("var", name)
        new_body = substitute(body, varname, fresh_var)
        return state.add_subgoals([(ctx, new_body)])
    else:
        raise Exception("intro tactic failed: goal is not implication or forall")

def tactic_exact(state: ProofState, term: Union[str, Prop]) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current

    # If term is string, check if it's a hypothesis name
    if isinstance(term, str):
        hyp = next((f for n, f in ctx if n == term), None)
        if hyp and prop_eq(hyp, goal):
            # Goal matches hypothesis
            return ProofState(state.goals[:-1])
        else:
            # Try parsing term as formula, if parser supports it
            formula = parse_formula(term)
            if prop_eq(formula, goal):
                return ProofState(state.goals[:-1])
            else:
                raise Exception("exact tactic failed: term doesn't match goal or not in context")
    else:
        # term is formula
        if prop_eq(term, goal):
            return ProofState(state.goals[:-1])
        else:
            raise Exception("exact tactic failed: formula doesn't match goal")

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

def tactic_left(state: ProofState) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    if goal[0] == "or":
        return state.add_subgoals([(ctx, goal[1])])
    else:
        raise Exception("left tactic failed: goal is not disjunction")

def tactic_right(state: ProofState) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    if goal[0] == "or":
        return state.add_subgoals([(ctx, goal[2])])
    else:
        raise Exception("right tactic failed: goal is not disjunction")

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

def tactic_contradiction(state: ProofState) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, _ = current
    if any(hyp[1][0] == "bottom" for hyp in ctx):
        return ProofState(state.goals[:-1])
    else:
        raise Exception("contradiction failed: ⊥ not in context")

def tactic_assume(state: ProofState, prop: Prop) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current

    # Generate fresh name Hn not in ctx
    existing_names = {name for name, _ in ctx}
    n = 1
    while True:
        name = f"H{n}"
        if name not in existing_names:
            break
        n += 1

    new_ctx = ctx + [(name, prop)]
    return state.add_subgoals([(new_ctx, goal)])

def tactic_rename(state: ProofState, old_name: str, new_name: str) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current

    # Check old_name exists, and new_name does not clash
    names = [name for name, _ in ctx]
    if old_name not in names:
        raise Exception(f"rename failed: hypothesis '{old_name}' not found")
    if new_name in names:
        raise Exception(f"rename failed: hypothesis '{new_name}' already exists")

    new_ctx = [(new_name if name == old_name else name, prop) for name, prop in ctx]
    return state.add_subgoals([(new_ctx, goal)])


def tactic_clear(state: ProofState, name: str) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current

    new_ctx = [(n, p) for (n, p) in ctx if n != name]
    if len(new_ctx) == len(ctx):
        raise Exception(f"clear failed: hypothesis '{name}' not found")

    return state.add_subgoals([(new_ctx, goal)])

def tactic_not_intro(state: ProofState, name: str = "H") -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    if goal[0] != "not":
        raise Exception("not_intro tactic failed: goal is not a negation ¬P")
    p = goal[1]
    # Add p as hypothesis with given name, goal becomes bottom
    new_ctx = ctx + [(name, p)]
    return state.add_subgoals([(new_ctx, ("bottom",))])

def tactic_not_elim(state: ProofState, hyp_name: str) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current

    hyp = next((f for n, f in ctx if n == hyp_name), None)
    if hyp is None:
        raise Exception(f"not_elim failed: hypothesis '{hyp_name}' not found")

    # hyp should be ¬¬P represented as ('not', ('not', P))
    if isinstance(hyp, tuple) and hyp[0] == 'not':
        inner = hyp[1]
        if isinstance(inner, tuple) and inner[0] == 'not':
            P = inner[1]
            if prop_eq(P, goal):
                # Remove current goal and add no subgoals (conclude goal)
                return ProofState(state.goals[:-1])
            else:
                raise Exception("not_elim failed: goal doesn't match ¬¬P inner proposition")
        else:
            raise Exception("not_elim failed: hypothesis is not double negation")
    else:
        raise Exception("not_elim failed: hypothesis is not negation")



def tactic_assumption(state: ProofState) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    for name, hyp in reversed(ctx):
        if prop_eq(hyp, goal):
            return ProofState(state.goals[:-1])
    raise Exception("assumption failed: no matching hypothesis")

def simplify_prop(p: Prop) -> Prop:
    # Basic simplifications (extend as needed)
    tag = p[0]
    if tag in ("implies", "and", "or"):
        left = simplify_prop(p[1])
        right = simplify_prop(p[2])
        if tag == "implies" and prop_eq(left, right):
            # P → P is True (replace with a tautology, or just keep)
            return ("implies", left, right)  # or a const True if you add it
        if tag == "and":
            # Simplify ⊥ ∧ P or P ∧ ⊥ to ⊥
            if left[0] == "bottom" or right[0] == "bottom":
                return ("bottom",)
        return (tag, left, right)
    elif tag == "not":
        inner = simplify_prop(p[1])
        return ("not", inner)
    elif tag in ("forall", "exists"):
        varname, body = p[1], simplify_prop(p[2])
        return (tag, varname, body)
    else:
        return p

def tactic_simplify(state: ProofState) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    new_goal = simplify_prop(goal)
    if prop_eq(new_goal, goal):
        raise Exception("simplify failed: no simplification possible")
    return state.add_subgoals([(ctx, new_goal)])

def tactic_auto(state: ProofState) -> ProofState:
    try:
        return tactic_assumption(state)
    except Exception:
        pass
    try:
        return tactic_contradiction(state)
    except Exception:
        pass
    try:
        return tactic_split(state)
    except Exception:
        pass
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    _, goal = current
    if goal[0] in ("implies", "forall"):
        try:
            return tactic_intro(state)
        except Exception:
            pass
    raise Exception("auto tactic failed")

def tactic_dne(state: ProofState, hyp_name: str = "H") -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current

    # Try to find hypothesis ¬¬P where P = goal
    for name, prop in ctx:
        if name == hyp_name and prop[0] == "not" and prop[1][0] == "not":
            inner = prop[1][1]
            if prop_eq(inner, goal):
                return ProofState(state.goals[:-1])  # discharge goal
    raise Exception("dne tactic failed: hypothesis ¬¬P not found")

def tactic_apply(state: ProofState, arg: str) -> ProofState:
    if not state.goals:
        raise ProofError("No goals to apply tactic to.")

    context, goal = state.goals[0]

    # Try to find the hypothesis named `arg`
    hyp_formula = None
    for name, formula in context:
        if name == arg:
            hyp_formula = formula
            break

    if hyp_formula is None:
        raise ProofError(f"apply tactic failed: hypothesis '{arg}' not found.")

    if not (isinstance(hyp_formula, tuple) and hyp_formula[0] == 'imp'):
        raise ProofError(f"apply tactic failed: hypothesis '{arg}' is not an implication.")

    A, B = hyp_formula[1], hyp_formula[2]

    if not formulas_equal(B, goal):
        raise ProofError(f"apply tactic failed: conclusion of '{arg}' does not match goal.")

    # Replace the current goal with A
    new_goals = [(context, A)] + state.goals[1:]
    return ProofState(new_goals)

def tactic_assumption(state: ProofState) -> ProofState:
    current = state.current()
    if current is None:
        raise Exception("No current goal")
    ctx, goal = current
    for n, hyp in ctx:
        if prop_eq(hyp, goal):
            return ProofState(state.goals[:-1])
    raise Exception("assumption tactic failed: no hypothesis matches goal")

def safe_tactic_call(tactic_func, state, *args, **kwargs):
    try:
        return tactic_func(state, *args, **kwargs)
    except Exception as e:
        if state is None or state.is_complete():
            print(f"Error: {str(e)}")
        else:
            ctx, goal = state.current()
            print(f"Error: {str(e)}")
            print("Current hypotheses:")
            if not ctx:
                print("  ∅")
            else:
                for n, f in ctx:
                    print(f"  {n} : {prop_repr(f)}")
            print(f"Current goal: {prop_repr(goal)}")
        return state

def parse_formula(formula_str: str) -> Prop:
    tokens = lex(formula_str)
    parser = Parser(tokens)
    return parser.parse()

# === Lexer and Parser ===

token_specification = [
    ('FORALL',   r'∀|forall'),
    ('EXISTS',   r'∃|exists'),
    ('NOT',      r'¬|~|not'),
    ('BOTTOM', r'⊥|bottom'),
    ('AND',      r'∧|&|and'),
    ('OR',       r'∨|\||or'),
    ('IMPLIES',  r'→|->|implies'),
    ('DOT',      r'\.'),
    ('LPAREN',   r'\('),
    ('RPAREN',   r'\)'),
    ('COMMA',    r','),
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
        left = self.parse_or()
        while self.peek() and self.peek()[0] == 'IMPLIES':
            self.consume('IMPLIES')
            right = self.parse_implication()
            left = implies(left, right)
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
            return ("var", self.consume('VAR')[1])
        elif tok[0] == 'CONST':
            name = self.consume('CONST')[1]
            if self.peek() and self.peek()[0] == 'LPAREN':
                self.consume('LPAREN')
                args = self.parse_term_list()
                self.consume('RPAREN')
                return ("fun", name, args)
            else:
                return ("const", name)
        else:
            raise SyntaxError(f"Unexpected token in term: {tok}")
        
    def parse_assume(command: str):
        if not command.startswith("assume "):
            raise ValueError("Invalid assume command")

        bindings = command[len("assume "):]
        
        # Split on commas not inside parentheses
        parts = split_outside_parens(bindings, ',')

        result = []
        for part in parts:
            part = part.strip()
            if ':' not in part:
                raise ValueError(f"Expected ':' in assumption: {part}")
            name, formula_str = map(str.strip, part.split(':', 1))
            formula = parse_formula(formula_str)
            result.append((name, formula))
        return result


    def split_outside_parens(s, delimiter):
        result = []
        level = 0
        current = []

        for c in s:
            if c == '(':
                level += 1
            elif c == ')':
                level -= 1
            elif c == delimiter and level == 0:
                result.append(''.join(current))
                current = []
                continue
            current.append(c)

        if current:
            result.append(''.join(current))
        return result

# === Proof Assistant Controller ===

def print_help():
    print("""Available commands:
- goal <expr>                   : Set current goal, e.g. goal ∀x. P(x) → P(x)
- intro [name]                  : Introduce implication or forall
- exact <prop>                  : Solve with exact hypothesis
- split                        : Split conjunction goal
- destruct <index>             : Destruct ∧ or ∨ hypothesis at index (0-based)
- left / right                 : Solve disjunction goal
- forall_elim <index> <term>   : Instantiate ∀ hypothesis at index
- exists_intro <term>          : Provide witness for ∃ goal
- contradiction               : Solve from ⊥ in context
- assume <expr>                : Add hypothesis to context
- state                       : Show proof state
- exit                        : Quit
""")

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
            tokens = lex(arg)
            prop = Parser(tokens).parse()
            new_state = ProofState([([], prop)])
            print(f"Goal set: {prop_repr(prop)}")
            return new_state

        if state is None:
            print("No active proof. Use 'goal <expr>' to set a goal.")
            return None

        if cmd_name == "intro":
            name = arg if arg else "H"
            new_state = tactic_intro(state, name)
            print(new_state)
            return new_state

        elif cmd_name == "exact":
            if arg is None:
                print("Usage: exact <prop>")
                return state
            tokens = lex(arg)
            prop = Parser(tokens).parse()
            new_state = tactic_exact(state, prop)
            print(new_state)
            return new_state

        elif cmd_name == "split":
            new_state = tactic_split(state)
            print(new_state)
            return new_state

        elif cmd_name == "destruct":
            if arg is None or not arg.isdigit():
                print("Usage: destruct <index>")
                return state
            idx = int(arg)
            current = state.current()
            if current is None:
                print("No current goal")
                return state
            ctx, _ = current
            if idx < 0 or idx >= len(ctx):
                print("Invalid hypothesis index")
                return state
            hyp_name, _ = ctx[idx]
            new_state = tactic_destruct(state, hyp_name)
            print(new_state)
            return new_state

        elif cmd_name == "left":
            new_state = tactic_left(state)
            print(new_state)
            return new_state

        elif cmd_name == "right":
            new_state = tactic_right(state)
            print(new_state)
            return new_state

        elif cmd_name == "forall_elim":
            if arg is None:
                print("Usage: forall_elim <index> <term>")
                return state
            parts2 = arg.split(maxsplit=1)
            if len(parts2) != 2 or not parts2[0].isdigit():
                print("Usage: forall_elim <index> <term>")
                return state
            hyp_idx = int(parts2[0])
            term_str = parts2[1]
            term_tokens = lex(term_str)
            term_parsed = Parser(term_tokens).parse()
            if term_parsed[0] not in ("var", "const"):
                print("forall_elim term must be a variable or constant")
                return state
            new_state = tactic_forall_elim(state, hyp_idx, term_parsed)
            print(new_state)
            return new_state


        elif cmd_name == "exists_intro":
            if arg is None:
                print("Usage: exists_intro <term>")
                return state
            term_tokens = lex(arg)
            term_parsed = Parser(term_tokens).parse()
            if term_parsed[0] not in ("var", "const"):
                print("exists_intro term must be a variable or constant")
                return state
            new_state = tactic_exists_intro(state, term_parsed)
            print(new_state)
            return new_state

        elif cmd_name == "contradiction":
            new_state = tactic_contradiction(state)
            print(new_state)
            return new_state

        elif cmd_name == "assume":
            if arg is None:
                print("Usage: assume <expr>")
                return state
            tokens = lex(arg)
            prop = Parser(tokens).parse()
            new_state = tactic_assume(state, prop)
            print(new_state)
            return new_state

        elif cmd_name == "state":
            print(state)
            return state

        elif cmd_name == "exit":
            print("Exiting.")
            sys.exit(0)

        elif cmd_name == "context":
            current = state.current() if state else None
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

        elif cmd_name == "rename":
            if arg is None:
                print("Usage: rename <old_name> <new_name>")
                return state
            parts2 = arg.split()
            if len(parts2) != 2:
                print("Usage: rename <old_name> <new_name>")
                return state
            old_name, new_name = parts2
            new_state = tactic_rename(state, old_name, new_name)
            print(new_state)
            return new_state

        elif cmd_name == "clear":
            if arg is None:
                print("Usage: clear <name>")
                return state
            name = arg.strip()
            new_state = tactic_clear(state, name)
            print(new_state)
            return new_state
        
        elif cmd_name == "not_intro":
            name = arg if arg else "H"
            new_state = tactic_not_intro(state, name)
            print(new_state)
            return new_state

        elif cmd_name == "not_elim":
            if arg is None:
                print("Usage: not_elim <neg_hyp_name> <pos_hyp_name> [bottom_name]")
                return state
            parts2 = arg.split()
            if len(parts2) not in (2, 3):
                print("Usage: not_elim <neg_hyp_name> <pos_hyp_name> [bottom_name]")
                return state
            neg_name, pos_name = parts2[0], parts2[1]
            bottom_name = parts2[2] if len(parts2) == 3 else "Hbot"
            new_state = tactic_not_elim(state, neg_name, pos_name, bottom_name)
            print(new_state)
            return new_state

        elif cmd_name == "assumption":
            new_state = tactic_assumption(state)
            print(new_state)
            return new_state

        elif cmd_name == "simplify":
            new_state = tactic_simplify(state)
            print(new_state)
            return new_state

        elif cmd_name == "auto":
            new_state = tactic_auto(state)
            print(new_state)
            return new_state

        elif cmd_name == "dne":
            if arg is None:
                print("Usage: dne <hypothesis_name>")
                return state
            new_state = tactic_dne(state, arg)
            print(new_state)
            return new_state
        
        elif cmd_name == "assume":
            if arg is None:
                print("Usage: assume <name> : <formula> [, <name> : <formula> ...]")
                return state
            # Split by commas, then parse each "name : formula" pair
            assumptions = [part.strip() for part in arg.split(',')]
            if state is None:
                print("No active proof. Use 'goal <expr>' to set a goal.")
                return state
            ctx, goal = state.current()
            new_ctx = list(ctx)  # copy current context

            for assumption in assumptions:
                match = re.match(r"(\w+)\s*:\s*(.+)", assumption)
                if not match:
                    print(f"Invalid assumption syntax: '{assumption}'")
                    return state
                name, formula_str = match.groups()
                try:
                    formula = parse_formula(formula_str)
                except Exception as e:
                    print(f"Error parsing formula in assumption '{assumption}': {e}")
                    return state
                new_ctx.append((name, formula))

            new_goals = state.goals[:-1] + [(new_ctx, goal)]
            new_state = ProofState(new_goals)
            print(new_state)
            return new_state

        else:
            print(f"Unknown command: {cmd_name}")
            return state

    except Exception as e:
        print(f"Error: {e}")
        return state

def repl():
    print("🔍 Mini Proof Assistant (Functional Style)")
    print("Type 'help' for commands, 'exit' to quit.")
    state: Optional[ProofState] = None
    while True:
        try:
            cmd = input("proof> ")
        except EOFError:
            print("\nExiting.")
            break
        state = process_command(state, cmd)

def run_proof_file(filename: str, step_by_step=False):
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
    else:
        print(f"Usage: {sys.argv[0]} [prooffile|proofs_folder]")
        sys.exit(1)

if __name__ == "__main__":
    main()
