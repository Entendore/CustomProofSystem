import re
from typing import List, Tuple, Callable, Optional
import os
import sys
# === Logic AST Classes ===

class Prop:
    pass

class Term:
    pass

class VarT(Term):
    def __init__(self, name): self.name = name
    def __repr__(self): return self.name
    def __eq__(self, other): return isinstance(other, VarT) and self.name == other.name

class Const(Term):
    def __init__(self, name): self.name = name
    def __repr__(self): return self.name
    def __eq__(self, other): return isinstance(other, Const) and self.name == other.name

class Var(Prop):
    def __init__(self, name): self.name = name
    def __repr__(self): return self.name
    def __eq__(self, other): return isinstance(other, Var) and self.name == other.name

class Bottom(Prop):
    def __repr__(self): return "⊥"

class Predicate(Prop):
    def __init__(self, name, args: List[Term]):
        self.name = name
        self.args = args
    def __repr__(self): 
        if self.args:
            return f"{self.name}({', '.join(map(str, self.args))})"
        else:
            return self.name
    def __eq__(self, other):
        return isinstance(other, Predicate) and self.name == other.name and self.args == other.args

class Implies(Prop):
    def __init__(self, premise: Prop, conclusion: Prop):
        self.premise = premise
        self.conclusion = conclusion
    def __repr__(self): return f"({self.premise} → {self.conclusion})"
    def __eq__(self, other):
        return isinstance(other, Implies) and self.premise == other.premise and self.conclusion == other.conclusion

class And(Prop):
    def __init__(self, left: Prop, right: Prop):
        self.left = left
        self.right = right
    def __repr__(self): return f"({self.left} ∧ {self.right})"
    def __eq__(self, other):
        return isinstance(other, And) and self.left == other.left and self.right == other.right

class Or(Prop):
    def __init__(self, left: Prop, right: Prop):
        self.left = left
        self.right = right
    def __repr__(self): return f"({self.left} ∨ {self.right})"
    def __eq__(self, other):
        return isinstance(other, Or) and self.left == other.left and self.right == other.right

class Not(Prop):
    def __init__(self, prop: Prop):
        self.prop = prop
    def __repr__(self): return f"¬{self.prop}"
    def __eq__(self, other):
        return isinstance(other, Not) and self.prop == other.prop

class ForAll(Prop):
    def __init__(self, var: VarT, body: Prop):
        self.var = var
        self.body = body
    def __repr__(self): return f"(∀{self.var}. {self.body})"
    def __eq__(self, other): return isinstance(other, ForAll) and self.var == other.var and self.body == other.body

class Exists(Prop):
    def __init__(self, var: VarT, body: Prop):
        self.var = var
        self.body = body
    def __repr__(self): return f"(∃{self.var}. {self.body})"
    def __eq__(self, other): return isinstance(other, Exists) and self.var == other.var and self.body == other.body

# === Substitution utility ===

def substitute(prop: Prop, var: VarT, term: Term) -> Prop:
    if isinstance(prop, Predicate):
        new_args = [term if arg == var else arg for arg in prop.args]
        return Predicate(prop.name, new_args)
    elif isinstance(prop, ForAll):
        if prop.var == var:
            return prop
        return ForAll(prop.var, substitute(prop.body, var, term))
    elif isinstance(prop, Exists):
        if prop.var == var:
            return prop
        return Exists(prop.var, substitute(prop.body, var, term))
    elif isinstance(prop, Implies):
        return Implies(substitute(prop.premise, var, term), substitute(prop.conclusion, var, term))
    elif isinstance(prop, And):
        return And(substitute(prop.left, var, term), substitute(prop.right, var, term))
    elif isinstance(prop, Or):
        return Or(substitute(prop.left, var, term), substitute(prop.right, var, term))
    elif isinstance(prop, Not):
        return Not(substitute(prop.prop, var, term))
    else:
        return prop

# === Proof State and Tactics ===

Goal = Tuple[List[Prop], Prop]

class ProofState:
    def __init__(self, goals: List[Goal]):
        self.goals = goals
        self.proven = []

    def current(self) -> Optional[Goal]:
        return self.goals[-1] if self.goals else None

    def is_complete(self) -> bool:
        return len(self.goals) == 0

    def add_subgoals(self, new_goals: List[Goal]):
         self.goals = self.goals[:-1] + new_goals

    def __repr__(self):
        if self.is_complete():
            return "Proof complete."
        lines = []
        for i, (ctx, goal) in enumerate(self.goals):
            ctx_str = ', '.join(map(str, ctx)) if ctx else "∅"
            lines.append(f"Goal {i+1}: {ctx_str} ⊢ {goal}")
        return "\n".join(lines)

# Tactic type
Tactic = Callable[[ProofState], ProofState]

def intro(name="H") -> Tactic:
    def tactic(state: ProofState) -> ProofState:
        ctx, goal = state.current()
        if isinstance(goal, Implies):
            new_ctx = ctx + [goal.premise]
            new_goal = goal.conclusion
            state.add_subgoals([(new_ctx, new_goal)])
        elif isinstance(goal, ForAll):
            fresh_var = VarT(name)
            new_body = substitute(goal.body, goal.var, fresh_var)
            state.add_subgoals([(ctx, new_body)])
        else:
            raise Exception("intro tactic failed: goal is not → or ∀")
        return state
    return tactic

def exact(term: Prop) -> Tactic:
    def tactic(state: ProofState) -> ProofState:
        ctx, goal = state.current()
        if term in ctx and term == goal:
            state.goals.pop()
        else:
            raise Exception("exact tactic failed: term doesn't match goal or not in context")
        return state
    return tactic

def apply(implication: Prop) -> Tactic:
    def tactic(state: ProofState) -> ProofState:
        ctx, goal = state.current()
        if isinstance(implication, Implies) and implication.conclusion == goal:
            state.add_subgoals([(ctx, implication.premise)])
        else:
            raise Exception("apply tactic failed")
        return state
    return tactic

def split() -> Tactic:
    def tactic(state: ProofState) -> ProofState:
        ctx, goal = state.current()
        if isinstance(goal, And):
            state.add_subgoals([(ctx, goal.left), (ctx, goal.right)])
        else:
            raise Exception("split tactic failed: goal is not a conjunction")
        return state
    return tactic

def destruct(index: int) -> Tactic:
    def tactic(state: ProofState) -> ProofState:
        ctx, goal = state.current()
        hyp = ctx[index]
        new_ctx = ctx[:index] + ctx[index+1:]
        if isinstance(hyp, And):
            new_ctx += [hyp.left, hyp.right]
            state.add_subgoals([(new_ctx, goal)])
        elif isinstance(hyp, Or):
            ctx1 = new_ctx + [hyp.left]
            ctx2 = new_ctx + [hyp.right]
            state.add_subgoals([(ctx1, goal), (ctx2, goal)])
        else:
            raise Exception("destruct tactic failed: hypothesis is not ∧ or ∨")
        return state
    return tactic

def left() -> Tactic:
    def tactic(state: ProofState) -> ProofState:
        ctx, goal = state.current()
        if isinstance(goal, Or):
            state.add_subgoals([(ctx, goal.left)])
        else:
            raise Exception("left tactic failed: goal is not a disjunction")
        return state
    return tactic

def right() -> Tactic:
    def tactic(state: ProofState) -> ProofState:
        ctx, goal = state.current()
        if isinstance(goal, Or):
            state.add_subgoals([(ctx, goal.right)])
        else:
            raise Exception("right tactic failed: goal is not a disjunction")
        return state
    return tactic

def forall_elim(hyp_index: int, term: Term) -> Tactic:
    def tactic(state: ProofState) -> ProofState:
        ctx, goal = state.current()
        hyp = ctx[hyp_index]
        if isinstance(hyp, ForAll):
            new_prop = substitute(hyp.body, hyp.var, term)
            new_ctx = ctx + [new_prop]
            state.add_subgoals([(new_ctx, goal)])
        else:
            raise Exception("forall_elim failed: not a ∀ hypothesis")
        return state
    return tactic

def exists_intro(term: Term) -> Tactic:
    def tactic(state: ProofState) -> ProofState:
        ctx, goal = state.current()
        if isinstance(goal, Exists):
            new_goal = substitute(goal.body, goal.var, term)
            state.add_subgoals([(ctx, new_goal)])
        else:
            raise Exception("exists_intro failed: goal is not an existential")
        return state
    return tactic

def contradiction() -> Tactic:
    def tactic(state: ProofState) -> ProofState:
        ctx, _ = state.current()
        if any(isinstance(h, Bottom) for h in ctx):
            state.goals.pop()
        else:
            raise Exception("contradiction failed: ⊥ not in context")
        return state
    return tactic

def assume(prop: Prop) -> Tactic:
    def tactic(state: ProofState) -> ProofState:
        ctx, goal = state.current()
        new_ctx = ctx + [prop]
        state.add_subgoals([(new_ctx, goal)])
        return state
    return tactic

# === Lexer ===

token_specification = [
    ('FORALL',   r'∀|forall'),
    ('EXISTS',   r'∃|exists'),
    ('NOT',      r'¬|~|not'),
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

def lex(characters: str) -> List[Tuple[str, Optional[str]]]:
    tokens = []
    for mo in token_re.finditer(characters):
        kind = mo.lastgroup
        value = mo.group()
        if kind == 'SKIP':
            continue
        elif kind == 'MISMATCH':
            raise SyntaxError(f'Unexpected character {value!r}')
        else:
            tokens.append((kind, value))
    return tokens

# === Parser ===

class Parser:
    def __init__(self, tokens: List[Tuple[str, Optional[str]]]):
        self.tokens = tokens
        self.pos = 0

    def peek(self) -> Optional[Tuple[str, Optional[str]]]:
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def consume(self, expected_type=None) -> Tuple[str, Optional[str]]:
        token = self.peek()
        if token is None:
            raise SyntaxError("Unexpected end of input")
        if expected_type and token[0] != expected_type:
            raise SyntaxError(f"Expected {expected_type}, got {token[0]}")
        self.pos += 1
        return token

    def parse(self):
        result = self.parse_implication()
        if self.peek() is not None:
            raise SyntaxError("Unexpected token after end of expression")
        return result

    def parse_implication(self):
        left = self.parse_or()
        while self.peek() and self.peek()[0] == 'IMPLIES':
            self.consume('IMPLIES')
            right = self.parse_implication()
            left = Implies(left, right)
        return left

    def parse_or(self):
        left = self.parse_and()
        while self.peek() and self.peek()[0] == 'OR':
            self.consume('OR')
            right = self.parse_and()
            left = Or(left, right)
        return left

    def parse_and(self):
        left = self.parse_not()
        while self.peek() and self.peek()[0] == 'AND':
            self.consume('AND')
            right = self.parse_not()
            left = And(left, right)
        return left

    def parse_not(self):
        if self.peek() and self.peek()[0] == 'NOT':
            self.consume('NOT')
            prop = self.parse_not()
            return Not(prop)
        else:
            return self.parse_quantifier_or_atomic()

    def parse_quantifier_or_atomic(self):
        tok = self.peek()
        if tok and tok[0] == 'FORALL':
            self.consume('FORALL')
            var_token = self.consume('VAR')
            self.consume('DOT')
            body = self.parse_implication()
            return ForAll(VarT(var_token[1]), body)
        elif tok and tok[0] == 'EXISTS':
            self.consume('EXISTS')
            var_token = self.consume('VAR')
            self.consume('DOT')
            body = self.parse_implication()
            return Exists(VarT(var_token[1]), body)
        else:
            return self.parse_atomic()

    def parse_atomic(self):
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
                return Predicate(pred_name, args)
            else:
                return Predicate(pred_name, [])
        elif tok[0] == 'VAR':
            var_name = self.consume('VAR')[1]
            return VarT(var_name)
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
            return VarT(self.consume('VAR')[1])
        elif tok[0] == 'CONST':
            return Const(self.consume('CONST')[1])
        else:
            raise SyntaxError(f"Unexpected token in term: {tok}")

# === Interactive CLI ===

def tactic_repl():
    print("🔍 Mini Proof Assistant (Tactic Mode)")
    print("Type 'help' for commands, 'exit' to quit.")
    state = None

    while True:
        try:
            command = input("proof> ").strip()
        except EOFError:
            break

        if command == "exit":
            break
        elif command == "help":
            print("""Available commands:
- goal <expr>                   : Set current goal, e.g. goal ∀x. P(x) → P(x)
- intro [name]                  : Introduce implication or forall
- exact <prop>                  : Solve with exact hypothesis
- split                        : Split conjunction goal
- destruct <index>             : Destruct ∧ or ∨ hypothesis at index
- left / right                 : Solve disjunction goal
- forall_elim <index> <term>   : Instantiate ∀ hypothesis
- exists_intro <term>          : Provide witness for ∃ goal
- contradiction               : Solve from ⊥ in context
- assume <expr>                : Add hypothesis to context
- state                       : Show proof state
- exit                        : Quit
""")
        elif command.startswith("goal "):
            expr_str = command[5:].strip()
            try:
                tokens = lex(expr_str)
                parser = Parser(tokens)
                prop = parser.parse()
                state = ProofState([([], prop)])
                print(f"Goal set: {prop}")
            except Exception as e:
                print(f"Parse error: {e}")

        elif command.startswith("intro"):
            if state is None:
                print("Set a goal first with 'goal ...'")
                continue
            try:
                state = intro()(state)
                print(state)
            except Exception as e:
                print(e)

        elif command.startswith("exact"):
            if state is None:
                print("Set a goal first")
                continue
            prop_str = command[len("exact "):].strip()
            # Try to parse prop from string, or match hypotheses by name
            try:
                tokens = lex(prop_str)
                parser = Parser(tokens)
                prop = parser.parse()
            except Exception as e:
                print(f"Parse error in exact argument: {e}")
                continue
            try:
                state = exact(prop)(state)
                print(state)
            except Exception as e:
                print(e)

        elif command == "split":
            if state is None:
                print("Set a goal first")
                continue
            try:
                state = split()(state)
                print(state)
            except Exception as e:
                print(e)

        elif command.startswith("destruct"):
            if state is None:
                print("Set a goal first")
                continue
            try:
                idx = int(command.split()[1])
                state = destruct(idx)(state)
                print(state)
            except Exception as e:
                print(e)

        elif command == "left":
            if state is None:
                print("Set a goal first")
                continue
            try:
                state = left()(state)
                print(state)
            except Exception as e:
                print(e)

        elif command == "right":
            if state is None:
                print("Set a goal first")
                continue
            try:
                state = right()(state)
                print(state)
            except Exception as e:
                print(e)

        elif command.startswith("forall_elim"):
            if state is None:
                print("Set a goal first")
                continue
            try:
                parts = command.split()
                hyp_idx = int(parts[1])
                term_str = parts[2]
                term_tokens = lex(term_str)
                term_parser = Parser(term_tokens)
                term = term_parser.parse()
                if not isinstance(term, (VarT, Const)):
                    print("forall_elim term must be a variable or constant")
                    continue
                state = forall_elim(hyp_idx, term)(state)
                print(state)
            except Exception as e:
                print(e)

        elif command.startswith("exists_intro"):
            if state is None:
                print("Set a goal first")
                continue
            try:
                term_str = command.split()[1]
                term_tokens = lex(term_str)
                term_parser = Parser(term_tokens)
                term = term_parser.parse()
                if not isinstance(term, (VarT, Const)):
                    print("exists_intro term must be a variable or constant")
                    continue
                state = exists_intro(term)(state)
                print(state)
            except Exception as e:
                print(e)

        elif command == "contradiction":
            if state is None:
                print("Set a goal first")
                continue
            try:
                state = contradiction()(state)
                print(state)
            except Exception as e:
                print(e)

        elif command.startswith("assume"):
            if state is None:
                print("Set a goal first")
                continue
            try:
                expr_str = command[len("assume "):].strip()
                tokens = lex(expr_str)
                parser = Parser(tokens)
                prop = parser.parse()
                state = assume(prop)(state)
                print(state)
            except Exception as e:
                print(e)

        elif command == "state":
            if state is None:
                print("No active proof.")
            else:
                print(state)

        else:
            print("Unknown command, type 'help'.")


def run_proof_file(filename: str, state: Optional[ProofState] = None) -> ProofState:
    """
    Run commands from a proof script file.
    Each line is treated like a user input command in the REPL.
    Returns final ProofState.
    """
    if state is None:
        state = None

    print(f"Running proof script: {filename}")
    with open(filename, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    for lineno, line in enumerate(lines, 1):
        command = line.strip()
        if not command or command.startswith('#'):  # allow comment lines
            continue
        print(f">>> {command}")
        try:
            # We'll reuse the same command parsing logic from tactic_repl:
            # But here, to avoid duplicating code, create a helper function for commands:
            state = process_command(command, state)
        except Exception as e:
            print(f"Error in {filename} line {lineno}: {e}")
            break

        if state is not None and state.is_complete():
            print("Proof complete!")
            break

    if state is None:
        print("No proof state generated.")
    else:
        print(state)
    print("----- End of proof script -----\n")
    return state


def process_command(command: str, state: Optional[ProofState]) -> Optional[ProofState]:
    """
    Process a single command string given the current proof state,
    returning the updated proof state or None.
    This is mostly extracted from your REPL code for reuse.
    """
    if command == "exit":
        sys.exit(0)
    elif command.startswith("goal "):
        expr_str = command[5:].strip()
        tokens = lex(expr_str)
        parser = Parser(tokens)
        prop = parser.parse()
        state = ProofState([([], prop)])
        print(f"Goal set: {prop}")
    elif command.startswith("intro"):
        if state is None:
            print("Set a goal first with 'goal ...'")
            return state
        state = intro()(state)
        print(state)
    elif command.startswith("exact"):
        if state is None:
            print("Set a goal first")
            return state
        prop_str = command[len("exact "):].strip()
        tokens = lex(prop_str)
        parser = Parser(tokens)
        prop = parser.parse()
        state = exact(prop)(state)
        print(state)
    elif command == "split":
        if state is None:
            print("Set a goal first")
            return state
        state = split()(state)
        print(state)
    elif command.startswith("destruct"):
        if state is None:
            print("Set a goal first")
            return state
        idx = int(command.split()[1])
        state = destruct(idx)(state)
        print(state)
    elif command == "left":
        if state is None:
            print("Set a goal first")
            return state
        state = left()(state)
        print(state)
    elif command == "right":
        if state is None:
            print("Set a goal first")
            return state
        state = right()(state)
        print(state)
    elif command.startswith("forall_elim"):
        if state is None:
            print("Set a goal first")
            return state
        parts = command.split()
        hyp_idx = int(parts[1])
        term_str = parts[2]
        term_tokens = lex(term_str)
        term_parser = Parser(term_tokens)
        term = term_parser.parse()
        if not isinstance(term, (VarT, Const)):
            print("forall_elim term must be a variable or constant")
            return state
        state = forall_elim(hyp_idx, term)(state)
        print(state)
    elif command.startswith("exists_intro"):
        if state is None:
            print("Set a goal first")
            return state
        term_str = command.split()[1]
        term_tokens = lex(term_str)
        term_parser = Parser(term_tokens)
        term = term_parser.parse()
        if not isinstance(term, (VarT, Const)):
            print("exists_intro term must be a variable or constant")
            return state
        state = exists_intro(term)(state)
        print(state)
    elif command == "contradiction":
        if state is None:
            print("Set a goal first")
            return state
        state = contradiction()(state)
        print(state)
    elif command.startswith("assume"):
        if state is None:
            print("Set a goal first")
            return state
        expr_str = command[len("assume "):].strip()
        tokens = lex(expr_str)
        parser = Parser(tokens)
        prop = parser.parse()
        state = assume(prop)(state)
        print(state)
    elif command == "state":
        if state is None:
            print("No active proof.")
        else:
            print(state)
    else:
        print(f"Unknown command: {command}. Type 'help' for available commands.")
    return state


def run_proofs_in_folder(folder_path: str):
    """
    Run all proof files (*.txt or *.proof) in the folder.
    """
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


# === Main ===

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Mini Proof Assistant")
    parser.add_argument('--file', '-f', help="Run proof commands from a file")
    parser.add_argument('--folder', '-d', help="Run proof commands from all files in a folder")
    args = parser.parse_args()

    if args.file:
        run_proof_file(args.file)
    elif args.folder:
        run_proofs_in_folder(args.folder)
    else:
        tactic_repl()
