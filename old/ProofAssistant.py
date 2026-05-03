import re
import os
import sys
import json
import logging
import datetime
import readline
from typing import List, Tuple, Optional, Dict, Any, Union, Callable, Set
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

# === AST Definitions ===
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
            ProofSystem.COQ: {
                "use_ssr": False,
                "indent": 2,
                "include_imports": True
            },
            ProofSystem.ISABELLE: {
                "theory_name": "My_Theory",
                "indent": 2,
                "include_headers": True
            },
            ProofSystem.LEAN: {
                "use_structured_proofs": True,
                "indent": 2,
                "include_imports": True
            }
        }

    def record_step(self, tactic_name: str, arguments: List[Any], 
                   state_before: 'ProofState', state_after: 'ProofState',
                   success: bool = True, error_message: Optional[str] = None):
        step = ProofStep(
            tactic_name=tactic_name,
            arguments=arguments,
            subgoals_before=deepcopy(state_before.goals),
            subgoals_after=deepcopy(state_after.goals),
            success=success,
            error_message=error_message
        )
        self.steps.append(step)
        logger.info(f"Recorded step: {tactic_name} with {len(arguments)} args. Goals: {len(state_before.goals)} → {len(state_after.goals)}")

    def set_initial_goal(self, goal: Goal, theorem_name: str = "theorem"):
        self.initial_goal = deepcopy(goal)
        self.theorem_name = theorem_name

    def pretty_print(self):
        if not self.steps:
            print("No proof steps recorded")
            return
        print("Proof steps:")
        for i, step in enumerate(self.steps):
            status = "✓" if step.success else "✗"
            print(f"{i+1}. [{status}] {step.tactic_name} {step.arguments}")
            print(f"   Goals: {len(step.subgoals_before)} → {len(step.subgoals_after)}")
            if not step.success and step.error_message:
                print(f"   Error: {step.error_message}")

    def export_coq(self) -> str:
        """Export proof to Coq syntax with proper tactic mapping"""
        if not self.initial_goal or not self.steps:
            return ""
        options = self.export_options[ProofSystem.COQ]
        indent = " " * options["indent"]
        coq_lines = []
        # Add imports if needed
        if options["include_imports"]:
            coq_lines.extend([
                "Require Import Coq.Logic.Classical_Prop.",
                "Require Import Coq.Setoids.Setoid.",
                ""
            ])
        # Process initial goal
        ctx, goal = self.initial_goal
        # Generate hypotheses from context
        hypotheses = []
        for name, formula in ctx:
            hypotheses.append(f"({name} : {prop_to_coq(formula)})")
        # Theorem statement
        if hypotheses:
            coq_lines.append(f"Theorem {self.theorem_name} {' '.join(hypotheses)} : {prop_to_coq(goal)}.")
        else:
            coq_lines.append(f"Theorem {self.theorem_name} : {prop_to_coq(goal)}.")
        coq_lines.append("Proof.")
        # Process tactics
        for step in self.steps:
            if not step.success:
                coq_lines.append(f"{indent}(* Failed tactic: {step.tactic_name} {step.arguments} *)")
                continue
            coq_cmd = tactic_to_coq(step.tactic_name, step.arguments)
            if coq_cmd:
                coq_lines.append(f"{indent}{coq_cmd}.")
            else:
                coq_lines.append(f"{indent}(* No direct Coq equivalent for {step.tactic_name} *)")
        coq_lines.append("Qed.")
        coq_lines.append(f"(* Proof completed on {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')} *)")
        return "\n".join(coq_lines)

    def export_isabelle(self) -> str:
        """Export proof to Isabelle/HOL syntax"""
        if not self.initial_goal or not self.steps:
            return ""
        options = self.export_options[ProofSystem.ISABELLE]
        indent = " " * options["indent"]
        isabelle_lines = []
        # Add theory header if needed
        if options["include_headers"]:
            theory_name = options["theory_name"]
            isabelle_lines.extend([
                f"theory {theory_name}",
                "  imports Main",
                "begin",
                ""
            ])
        # Process initial goal
        ctx, goal = self.initial_goal
        # Generate assumptions from context
        assumptions = []
        for name, formula in ctx:
            assumptions.append(f"\"{prop_to_isabelle(formula)}\"")
        # Theorem statement
        theorem_header = f"theorem {self.theorem_name}"
        if assumptions:
            theorem_header += f":\n{indent}assumes {' '.join([f'A{i}' for i in range(len(assumptions))])}: \"{'\"\n  and \"'.join(assumptions)}\""
            theorem_header += f"\n{indent}shows \"{prop_to_isabelle(goal)}\""
        else:
            theorem_header += f": \"{prop_to_isabelle(goal)}\""
        isabelle_lines.append(theorem_header)
        isabelle_lines.append("proof -")
        # Process tactics
        has_failed_step = False
        for step in self.steps:
            if not step.success:
                isabelle_lines.append(f"{indent}(* Failed tactic: {step.tactic_name} {step.arguments} *)")
                has_failed_step = True
                continue
            isabelle_cmd = tactic_to_isabelle(step.tactic_name, step.arguments)
            if isabelle_cmd:
                isabelle_lines.append(f"{indent}{isabelle_cmd}")
            else:
                isabelle_lines.append(f"{indent}(* No direct Isabelle equivalent for {step.tactic_name} *)")
        # Complete the proof
        if not has_failed_step:
            isabelle_lines.append(f"{indent}qed")
        else:
            isabelle_lines.append(f"{indent}oops (* Proof incomplete due to failed tactics *)")
        # Add theory footer if needed
        if options["include_headers"]:
            isabelle_lines.extend([
                "",
                "end"
            ])
        return "\n".join(isabelle_lines)

    def export_lean(self) -> str:
        """Export proof to Lean 4 syntax"""
        if not self.initial_goal or not self.steps:
            return ""
        options = self.export_options[ProofSystem.LEAN]
        indent = " " * options["indent"]
        lean_lines = []
        # Add imports if needed
        if options["include_imports"]:
            lean_lines.extend([
                "import Mathlib",
                "import Mathlib.Tactic",
                ""
            ])
        # Process initial goal
        ctx, goal = self.initial_goal
        # Generate hypotheses from context
        hypotheses = []
        for name, formula in ctx:
            hypotheses.append(f"({name} : {prop_to_lean(formula)})")
        # Theorem statement
        theorem_header = f"theorem {self.theorem_name}"
        if hypotheses:
            theorem_header += f" ({' '.join(hypotheses)})"
        theorem_header += f" : {prop_to_lean(goal)}"
        if options["use_structured_proofs"]:
            # Structured proof style
            lean_lines.append(theorem_header + " := by")
            # Process tactics
            has_failed_step = False
            for step in self.steps:
                if not step.success:
                    lean_lines.append(f"{indent}-- Failed tactic: {step.tactic_name} {step.arguments}")
                    has_failed_step = True
                    continue
                lean_cmd = tactic_to_lean(step.tactic_name, step.arguments)
                if lean_cmd:
                    lean_lines.append(f"{indent}{lean_cmd}")
                else:
                    lean_lines.append(f"{indent}-- No direct Lean equivalent for {step.tactic_name} {step.arguments}")
            if has_failed_step:
                lean_lines.append(f"{indent}exact sorry")
        else:
            # Term mode proof
            lean_lines.append(theorem_header + " :=")
            lean_lines.append(f"{indent}by sorry -- Term mode proof export not fully implemented")
        lean_lines.append(f"\n-- Proof exported on {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        return "\n".join(lean_lines)

    def export_all(self, directory: str = ".") -> Dict[str, str]:
        """Export to all supported theorem provers and return a dictionary of results"""
        exports = {}
        # Ensure directory exists
        Path(directory).mkdir(parents=True, exist_ok=True)
        # Export to Coq
        coq_code = self.export_coq()
        exports["coq"] = coq_code
        if coq_code:
            coq_path = Path(directory) / f"{self.theorem_name}.v"
            with open(coq_path, "w") as f:
                f.write(coq_code)
            logger.info(f"Coq export saved to {coq_path}")
        # Export to Isabelle
        isabelle_code = self.export_isabelle()
        exports["isabelle"] = isabelle_code
        if isabelle_code:
            isabelle_path = Path(directory) / f"{self.theorem_name}.thy"
            with open(isabelle_path, "w") as f:
                f.write(isabelle_code)
            logger.info(f"Isabelle export saved to {isabelle_path}")
        # Export to Lean
        lean_code = self.export_lean()
        exports["lean"] = lean_code
        if lean_code:
            lean_path = Path(directory) / f"{self.theorem_name}.lean"
            with open(lean_path, "w") as f:
                f.write(lean_code)
            logger.info(f"Lean export saved to {lean_path}")
        return exports

    def save_proof_state(self, filename: str):
        """Save proof state to a file"""
        # Convert goals to serializable format
        def serialize_goal(goal: Goal) -> Dict:
            ctx, prop = goal
            return {
                "context": [(name, prop) for name, prop in ctx],
                "goal": prop
            }
        
        state = {
            "theorem_name": self.theorem_name,
            "initial_goal": serialize_goal(self.initial_goal) if self.initial_goal else None,
            "steps": [
                {
                    "tactic_name": step.tactic_name,
                    "arguments": step.arguments,
                    "success": step.success,
                    "error_message": step.error_message,
                    "timestamp": step.timestamp.isoformat()
                }
                for step in self.steps
            ],
            "export_options": {str(k.value): v for k, v in self.export_options.items()}
        }
        with open(filename, "w") as f:
            json.dump(state, f, indent=2)
        logger.info(f"Proof state saved to {filename}")

    def load_proof_state(self, filename: str):
        """Load proof state from a file"""
        with open(filename, "r") as f:
            state = json.load(f)
        self.theorem_name = state["theorem_name"]
        
        # Reconstruct initial goal
        if state["initial_goal"]:
            goal_data = state["initial_goal"]
            ctx = [(name, prop) for name, prop in goal_data["context"]]
            goal = goal_data["goal"]
            self.initial_goal = (ctx, goal)
        
        self.steps = []
        for step_data in state["steps"]:
            step = ProofStep(
                tactic_name=step_data["tactic_name"],
                arguments=step_data["arguments"],
                subgoals_before=[],  # These can't be fully restored from saved state
                subgoals_after=[],   # These can't be fully restored from saved state
                success=step_data["success"],
                error_message=step_data["error_message"],
                timestamp=datetime.datetime.fromisoformat(step_data["timestamp"])
            )
            self.steps.append(step)
        
        # Restore export options
        for system_str, options in state["export_options"].items():
            try:
                system = next(s for s in ProofSystem if s.value == system_str)
                self.export_options[system] = options
            except StopIteration:
                logger.warning(f"Unknown proof system in saved state: {system_str}")
        logger.info(f"Proof state loaded from {filename}")

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
        # Create a new state with the updated goals
        new_state = ProofState(self.goals[:-1] + new_goals, self.proof_tree)
        # Save the current state to history for undo functionality
        self.history.append((deepcopy(self.goals), deepcopy(self.proof_tree.steps)))
        self.future.clear()  # Clear redo history when making a new change
        return new_state

    def undo(self) -> Optional['ProofState']:
        """Undo the last proof step"""
        if not self.history:
            logger.warning("No actions to undo")
            return None
        # Save current state to future stack (for redo)
        self.future.append((deepcopy(self.goals), deepcopy(self.proof_tree.steps)))
        # Restore previous state
        previous_goals, previous_steps = self.history.pop()
        new_state = ProofState(deepcopy(previous_goals), deepcopy(self.proof_tree))
        new_state.proof_tree.steps = deepcopy(previous_steps)
        new_state.history = self.history.copy()
        new_state.future = self.future.copy()
        logger.info("Undo successful")
        return new_state

    def redo(self) -> Optional['ProofState']:
        """Redo the last undone proof step"""
        if not self.future:
            logger.warning("No actions to redo")
            return None
        # Save current state to history stack (for undo)
        self.history.append((deepcopy(self.goals), deepcopy(self.proof_tree.steps)))
        # Restore future state
        next_goals, next_steps = self.future.pop()
        new_state = ProofState(deepcopy(next_goals), deepcopy(self.proof_tree))
        new_state.proof_tree.steps = deepcopy(next_steps)
        new_state.history = self.history.copy()
        new_state.future = self.future.copy()
        logger.info("Redo successful")
        return new_state

    def __str__(self):
        if self.is_complete():
            return "✅ Proof complete."
        lines = []
        lines.append(f"Proof state: {len(self.goals)} remaining goal(s)")
        lines.append("=" * 50)
        for i, (ctx, goal) in enumerate(reversed(self.goals)):  # Show current goal last
            marker = ">>> " if i == 0 else "    "
            lines.append(f"{marker}Goal {len(self.goals)-i}:")
            lines.append(pretty_goal(ctx, goal))
            if i < len(self.goals) - 1:
                lines.append("-" * 50)
        return "\n".join(lines)

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
            args_str = ', '.join(term_repr(a) for a in args)
            return f"{name}({args_str})"
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
        case ("fun", name, args): 
            args_str = ', '.join(term_repr(a) for a in args)
            return f"{name}({args_str})"
        case ("lambda", params, body): return f"(λ{','.join(params)}. {term_repr(body)})"
        case ("app", f, a): return f"({term_repr(f)} {term_repr(a)})"
        case _: return str(t)

def pretty_context(ctx: Context) -> str:
    if not ctx:
        return "  Context: ∅"
    maxlen = max(len(name) for name, _ in ctx) if ctx else 0
    lines = [f"  {name.ljust(maxlen)} : {prop_repr(formula)}" for name, formula in ctx]
    return "  Context:\n" + "\n".join(lines)

def pretty_goal(ctx: Context, goal: Prop) -> str:
    return f"{pretty_context(ctx)}\n  Goal: {prop_repr(goal)}"

# === Substitution and Free Variables ===
def fresh_var(existing: set[str]) -> str:
    """Generate a fresh variable name not in the existing set"""
    base = "x"
    i = 1
    while f"{base}{i}" in existing:
        i += 1
    return f"{base}{i}"

def collect_vars_in_context(ctx: Context) -> set[str]:
    """Collect all variable names used in the context"""
    vars_set = set()
    for name, prop in ctx:
        vars_set.add(name)
        vars_set.update(free_vars(prop))
    return vars_set

def free_vars(prop: Prop) -> set[str]:
    match prop:
        case ('var', x): return {x}
        case ('const', _): return set()
        case ('pred', _, args): return set().union(*(free_vars_term(a) for a in args))
        case ('not', p): return free_vars(p)
        case ('and' | 'or' | 'implies', p, q): return free_vars(p) | free_vars(q)
        case ('forall' | 'exists', v, body): return free_vars(body) - {v}
        case ('bottom',): return set()
        case _: 
            logger.warning(f"Unexpected proposition type: {type(prop)}")
            return set()

def free_vars_term(t: Term) -> set[str]:
    match t:
        case ('var', x): return {x}
        case ('const', _): return set()
        case ('fun', _, args): return set().union(*(free_vars_term(a) for a in args))
        case ('lambda', params, body): return free_vars_term(body) - set(params)
        case ('app', f, a): return free_vars_term(f) | free_vars_term(a)
        case _: 
            logger.warning(f"Unexpected term type: {type(t)}")
            return set()

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

def term_eq(t1: Term, t2: Term) -> bool:
    match t1, t2:
        case ('var', x1), ('var', x2): return x1 == x2
        case ('const', c1), ('const', c2): return c1 == c2
        case ('fun', n1, args1), ('fun', n2, args2):
            if n1 != n2 or len(args1) != len(args2):
                return False
            return all(term_eq(a1, a2) for a1, a2 in zip(args1, args2))
        case ('lambda', params1, body1), ('lambda', params2, body2):
            if len(params1) != len(params2):
                return False
            fresh_params = [fresh_var(free_vars_term(body1) | free_vars_term(body2) | set(params1) | set(params2)) 
                           for _ in params1]
            body1_renamed = body1
            body2_renamed = body2
            for old1, old2, new in zip(params1, params2, fresh_params):
                body1_renamed = subst_term_var(body1_renamed, old1, new)
                body2_renamed = subst_term_var(body2_renamed, old2, new)
            return term_eq(body1_renamed, body2_renamed)
        case ('app', f1, a1), ('app', f2, a2):
            return term_eq(f1, f2) and term_eq(a1, a2)
        case _:
            return False

def generate_hypothesis_name(premise: Prop, ctx: Context) -> str:
    """Generate a meaningful name for a hypothesis based on the premise"""
    existing_names = {name for name, _ in ctx}
    
    match premise:
        case ('pred', name, _):
            base = name.lower()
        case ('not', _):
            base = "Hn"
        case ('and', _, _):
            base = "Hand"
        case ('or', _, _):
            base = "Hor"
        case ('implies', _, _):
            base = "Himp"
        case ('forall', v, _):
            base = f"Hall{v}"
        case ('exists', v, _):
            base = f"Hex{v}"
        case _:
            base = "H"
    
    # Find a unique name
    i = 1
    name = base
    while name in existing_names:
        name = f"{base}{i}"
        i += 1
        
    return name

# === Error Handling Decorator ===
def proof_tactic(func):
    """Decorator for proof tactics that handles errors and records steps properly"""
    @wraps(func)
    def wrapper(state: ProofState, *args, **kwargs) -> ProofState:
        state_before = ProofState(deepcopy(state.goals), state.proof_tree)
        try:
            # Create a copy of the state to avoid side effects in case of failure
            working_state = ProofState(deepcopy(state.goals), state.proof_tree)
            result = func(working_state, *args, **kwargs)
            # Copy history and future to preserve undo/redo capabilities
            result.history = state.history.copy()
            result.future = state.future.copy()
            # Record successful step
            state.proof_tree.record_step(func.__name__, list(args), state_before, result, success=True)
            return result
        except Exception as e:
            error_msg = str(e)
            logger.error(f"Tactic {func.__name__} failed: {error_msg}")
            # Record failed step
            state.proof_tree.record_step(func.__name__, list(args), state_before, state, 
                                        success=False, error_message=error_msg)
            # Re-raise the exception to be handled by the command processor
            raise
    return wrapper

# === Tactics with Error Handling ===
@proof_tactic
def tactic_intro(state: ProofState, name: Optional[str] = None) -> ProofState:
    """Introduce implication or universal quantifier"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    if goal[0] == "implies":
        premise, conclusion = goal[1], goal[2]
        # Generate a good name if not provided
        if name is None:
            name = generate_hypothesis_name(premise, ctx)
        # Check if name is already in context
        if any(n == name for n, _ in ctx):
            raise ValueError(f"Name '{name}' already exists in context")
        new_ctx = ctx + [(name, premise)]
        logger.info(f"Intro: assuming {prop_repr(premise)} as {name}")
        return state.add_subgoals([(new_ctx, conclusion)])
    elif goal[0] == "forall":
        varname, body = goal[1], goal[2]
        # Generate a fresh variable name
        all_vars = collect_vars_in_context(ctx) | free_vars(body)
        fresh_var_name = fresh_var(existing=all_vars)
        fresh_var_term = var(fresh_var_name)
        # Substitute the fresh variable into the body
        new_body = substitute(body, varname, fresh_var_term)
        logger.info(f"Intro: introducing fresh variable {fresh_var_name} for {varname}")
        return state.add_subgoals([(ctx, new_body)])
    elif goal[0] == "exists":
        # For exists, intro doesn't make sense - suggest exists_intro instead
        raise ValueError("intro tactic not applicable to existential quantifier. Use 'exists_intro <term>' instead")
    else:
        raise ValueError(f"intro tactic failed: goal is not implication or forall, but {goal[0]}")

@proof_tactic
def tactic_exact(state: ProofState, term: Union[str, Prop]) -> ProofState:
    """Solve the goal with an exact match from hypotheses or a formula"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    if isinstance(term, str):
        # Look for hypothesis with this name
        hyp = next((f for n, f in ctx if n == term), None)
        if hyp is None:
            existing_names = [n for n, _ in ctx]
            raise ValueError(f"exact tactic failed: no hypothesis named '{term}'. Available: {existing_names}")
        
        if alpha_eq(hyp, goal):
            return ProofState(state.goals[:-1], state.proof_tree)
        else:
            raise ValueError(f"exact tactic failed: hypothesis '{term}' doesn't match goal\n"
                           f"Hypothesis: {prop_repr(hyp)}\n"
                           f"Goal: {prop_repr(goal)}")
    else:
        # Check if term is a proposition that matches the goal
        if alpha_eq(term, goal):
            return ProofState(state.goals[:-1], state.proof_tree)
        else:
            raise ValueError(f"exact tactic failed: formula doesn't match goal\n"
                           f"Formula: {prop_repr(term)}\n"
                           f"Goal: {prop_repr(goal)}")

@proof_tactic
def tactic_split(state: ProofState) -> ProofState:
    """Split a conjunction goal into two subgoals"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    if goal[0] == "and":
        left, right = goal[1], goal[2]
        return state.add_subgoals([(ctx, left), (ctx, right)])
    else:
        raise ValueError(f"split tactic failed: goal is not conjunction, but {goal[0]}")

@proof_tactic
def tactic_destruct(state: ProofState, name: str) -> ProofState:
    """Perform case analysis on a hypothesis"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    # Find the hypothesis
    hyp_idx = -1
    hyp = None
    for i, (n, f) in enumerate(ctx):
        if n == name:
            hyp_idx = i
            hyp = f
            break
    
    if hyp is None:
        existing_names = [n for n, _ in ctx]
        raise ValueError(f"destruct tactic failed: no hypothesis named '{name}'. Available: {existing_names}")
    
    ctx_before = ctx[:hyp_idx]
    ctx_after = ctx[hyp_idx+1:]
    
    if hyp[0] == "and":
        # Split conjunction hypothesis into two parts
        left, right = hyp[1], hyp[2]
        left_name = f"{name}_left"
        right_name = f"{name}_right"
        new_ctx = ctx_before + [(left_name, left), (right_name, right)] + ctx_after
        return state.add_subgoals([(new_ctx, goal)])
    elif hyp[0] == "or":
        # Create two subgoals for disjunction case analysis
        left, right = hyp[1], hyp[2]
        left_ctx = ctx_before + [(f"{name}_case", left)] + ctx_after
        right_ctx = ctx_before + [(f"{name}_case", right)] + ctx_after
        return state.add_subgoals([(left_ctx, goal), (right_ctx, goal)])
    else:
        raise ValueError(f"destruct tactic failed: hypothesis '{name}' is not ∧ or ∨, but {hyp[0]}")

@proof_tactic
def tactic_left(state: ProofState) -> ProofState:
    """Solve a disjunction goal by proving the left component"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    if goal[0] == "or":
        left = goal[1]
        return state.add_subgoals([(ctx, left)])
    else:
        raise ValueError(f"left tactic failed: goal is not disjunction, but {goal[0]}")

@proof_tactic
def tactic_right(state: ProofState) -> ProofState:
    """Solve a disjunction goal by proving the right component"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    if goal[0] == "or":
        right = goal[2]
        return state.add_subgoals([(ctx, right)])
    else:
        raise ValueError(f"right tactic failed: goal is not disjunction, but {goal[0]}")

@proof_tactic
def tactic_forall_elim(state: ProofState, hyp_name: str, term_str: str) -> ProofState:
    """Instantiate a universal quantifier with a specific term"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    # Find the hypothesis
    hyp_idx = -1
    hyp = None
    for i, (n, f) in enumerate(ctx):
        if n == hyp_name:
            hyp_idx = i
            hyp = f
            break
    
    if hyp is None:
        existing_names = [n for n, _ in ctx]
        raise ValueError(f"forall_elim failed: no hypothesis named '{hyp_name}'. Available: {existing_names}")
    
    if hyp[0] != "forall":
        raise ValueError(f"forall_elim failed: hypothesis '{hyp_name}' is not ∀, but {hyp[0]}")
    
    # Parse the term
    try:
        term = parse_term(term_str)
    except Exception as e:
        raise ValueError(f"forall_elim failed: invalid term '{term_str}': {e}")
    
    varname, body = hyp[1], hyp[2]
    new_prop = substitute(body, varname, term)
    new_hyp_name = f"{hyp_name}_inst"
    
    # Check if name is already in context
    if any(n == new_hyp_name for n, _ in ctx):
        # Generate a unique name
        i = 1
        while any(n == f"{new_hyp_name}{i}" for n, _ in ctx):
            i += 1
        new_hyp_name = f"{new_hyp_name}{i}"
    
    new_ctx = ctx + [(new_hyp_name, new_prop)]
    logger.info(f"Forall elimination: instantiated {hyp_name} with {term_repr(term)} as {new_hyp_name}")
    return state.add_subgoals([(new_ctx, goal)])

@proof_tactic
def tactic_exists_intro(state: ProofState, term_str: str) -> ProofState:
    """Provide a witness for an existential quantifier"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    if goal[0] != "exists":
        raise ValueError(f"exists_intro failed: goal is not ∃, but {goal[0]}")
    
    # Parse the term
    try:
        term = parse_term(term_str)
    except Exception as e:
        raise ValueError(f"exists_intro failed: invalid term '{term_str}': {e}")
    
    varname, body = goal[1], goal[2]
    new_goal = substitute(body, varname, term)
    logger.info(f"Exists introduction: using witness {term_repr(term)}")
    return state.add_subgoals([(ctx, new_goal)])

@proof_tactic
def tactic_contradiction(state: ProofState) -> ProofState:
    """Solve the goal when ⊥ is in the context"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, _ = current
    
    # Check for bottom in context
    for name, hyp in ctx:
        if hyp[0] == "bottom":
            logger.info(f"Contradiction: found ⊥ as hypothesis {name}")
            return ProofState(state.goals[:-1], state.proof_tree)
    
    # Check for P and not P in context
    props = {}
    for name, hyp in ctx:
        props[name] = hyp
    
    for name1, p in props.items():
        for name2, q in props.items():
            if name1 != name2 and p[0] == "not" and alpha_eq(p[1], q):
                logger.info(f"Contradiction: found {name1} ({prop_repr(p)}) and {name2} ({prop_repr(q)})")
                return ProofState(state.goals[:-1], state.proof_tree)
    
    raise ValueError("contradiction failed: no contradiction found in context")

@proof_tactic
def tactic_assume(state: ProofState, prop_str: str) -> ProofState:
    """Add a new assumption to the context"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    # Parse the proposition
    try:
        prop = parse_formula(prop_str)
    except Exception as e:
        raise ValueError(f"assume failed: invalid formula '{prop_str}': {e}")
    
    # Generate a unique name for the hypothesis
    existing_names = {name for name, _ in ctx}
    base_name = generate_hypothesis_name(prop, ctx)
    
    new_ctx = ctx + [(base_name, prop)]
    logger.info(f"Assume: added hypothesis {base_name} : {prop_repr(prop)}")
    return state.add_subgoals([(new_ctx, goal)])

@proof_tactic
def tactic_rename(state: ProofState, old_name: str, new_name: str) -> ProofState:
    """Rename a hypothesis"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    # Check if new name already exists
    if any(n == new_name for n, _ in ctx):
        raise ValueError(f"rename failed: hypothesis '{new_name}' already exists")
    
    # Create new context with renamed hypothesis
    new_ctx = []
    found = False
    for name, prop in ctx:
        if name == old_name:
            new_ctx.append((new_name, prop))
            found = True
        else:
            new_ctx.append((name, prop))
    
    if not found:
        existing_names = [n for n, _ in ctx]
        raise ValueError(f"rename failed: hypothesis '{old_name}' not found. Available: {existing_names}")
    
    logger.info(f"Rename: {old_name} → {new_name}")
    return state.add_subgoals([(new_ctx, goal)])

@proof_tactic
def tactic_clear(state: ProofState, name: str) -> ProofState:
    """Remove a hypothesis from the context"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    new_ctx = [(n, p) for (n, p) in ctx if n != name]
    if len(new_ctx) == len(ctx):
        existing_names = [n for n, _ in ctx]
        raise ValueError(f"clear failed: hypothesis '{name}' not found. Available: {existing_names}")
    
    logger.info(f"Clear: removed hypothesis {name}")
    return state.add_subgoals([(new_ctx, goal)])

@proof_tactic
def tactic_not_intro(state: ProofState, name: str = "H") -> ProofState:
    """Prove a negation by assuming the positive and deriving a contradiction"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    if goal[0] != "not":
        raise ValueError(f"not_intro tactic failed: goal is not a negation ¬P, but {goal[0]}")
    
    p = goal[1]
    # Check if name is already in context
    if any(n == name for n, _ in ctx):
        raise ValueError(f"not_intro failed: name '{name}' already exists in context")
    
    new_ctx = ctx + [(name, p)]
    logger.info(f"Not intro: assuming {prop_repr(p)} as {name} to prove ⊥")
    return state.add_subgoals([(new_ctx, bottom())])

@proof_tactic
def tactic_assumption(state: ProofState) -> ProofState:
    """Solve the goal if it matches a hypothesis"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    for name, hyp in reversed(ctx):  # Check from most recent to oldest
        if alpha_eq(hyp, goal):
            logger.info(f"Assumption: using hypothesis {name} to solve goal")
            return ProofState(state.goals[:-1], state.proof_tree)
    
    # If no direct match, check for P and not P where goal is bottom
    if goal[0] == "bottom":
        props = {}
        for name, hyp in ctx:
            props[name] = hyp
        
        for name1, p in props.items():
            for name2, q in props.items():
                if name1 != name2 and p[0] == "not" and alpha_eq(p[1], q):
                    logger.info(f"Assumption: using contradiction between {name1} and {name2} to solve ⊥")
                    return ProofState(state.goals[:-1], state.proof_tree)
    
    existing_hyps = [f"{name} : {prop_repr(hyp)}" for name, hyp in ctx]
    raise ValueError(f"assumption tactic failed: no matching hypothesis for goal {prop_repr(goal)}\n"
                   f"Available hypotheses:\n" + "\n".join(existing_hyps))

@proof_tactic
def tactic_reflexivity(state: ProofState) -> ProofState:
    """Solve equality goals of the form t = t"""
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    if goal[0] == "pred" and goal[1] == "=" and len(goal[2]) == 2:
        left, right = goal[2]
        if term_eq(left, right):
            logger.info(f"Reflexivity: {term_repr(left)} = {term_repr(right)}")
            return ProofState(state.goals[:-1], state.proof_tree)
    
    raise ValueError(f"reflexivity failed: goal is not of the form t = t, but {prop_repr(goal)}")

@proof_tactic
def tactic_auto(state: ProofState, depth: int = 3) -> ProofState:
    """Attempt to automatically prove the goal using simple tactics"""
    if depth <= 0:
        raise ValueError("Auto depth exceeded")
    
    current = state.current()
    if current is None:
        raise ValueError("No current goal")
    ctx, goal = current
    
    # Try assumption first
    for name, hyp in reversed(ctx):
        if alpha_eq(hyp, goal):
            logger.info(f"Auto: solved by assumption ({name})")
            return ProofState(state.goals[:-1], state.proof_tree)
    
    # Try contradiction
    for name1, p in ctx:
        for name2, q in ctx:
            if name1 != name2 and p[0] == "not" and alpha_eq(p[1], q):
                logger.info(f"Auto: solved by contradiction between {name1} and {name2}")
                return ProofState(state.goals[:-1], state.proof_tree)
    
    # Match on goal shape
    match goal:
        case ('and', p, q):
            logger.info("Auto: splitting conjunction")
            state = tactic_split(state)
            # Apply auto to each subgoal
            for _ in range(2):  # We know split creates 2 subgoals
                if state.goals:
                    state = tactic_auto(ProofState(state.goals, state.proof_tree), depth - 1)
            return state
        case ('implies', p, q):
            logger.info("Auto: introducing implication")
            name = generate_hypothesis_name(p, ctx)
            state = tactic_intro(state, name)
            return tactic_auto(state, depth - 1)
        case ('forall', v, body):
            logger.info("Auto: introducing universal quantifier")
            state = tactic_intro(state)
            return tactic_auto(state, depth - 1)
        case ('exists', v, body):
            # For exists, we need a witness - can't auto this easily
            pass
        case ('or', p, q):
            # Try left branch
            try:
                temp_state = tactic_left(ProofState(deepcopy(state.goals), state.proof_tree))
                return tactic_auto(temp_state, depth - 1)
            except:
                # Try right branch
                try:
                    temp_state = tactic_right(ProofState(deepcopy(state.goals), state.proof_tree))
                    return tactic_auto(temp_state, depth - 1)
                except:
                    pass
    
    # Try to use implications in context
    for name, hyp in ctx:
        if hyp[0] == 'implies':
            A, B = hyp[1], hyp[2]
            if alpha_eq(B, goal):
                # Try to prove A
                try:
                    temp_state = ProofState([(ctx, A)], state.proof_tree)
                    proved_subgoal = tactic_auto(temp_state, depth - 1)
                    if proved_subgoal.is_complete():
                        logger.info(f"Auto: using implication {name} after proving premise")
                        return tactic_exact(state, name)
                except:
                    continue
    
    raise ValueError(f"Auto tactic failed at depth {depth} for goal: {prop_repr(goal)}")

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
    
    def consume(self, expected_type: Optional[str] = None) -> Tuple[str, str]:
        token = self.peek()
        if token is None:
            raise SyntaxError("Unexpected end of input")
        if expected_type and token[0] != expected_type:
            raise SyntaxError(f"Expected {expected_type}, got {token[0]} at position {token[2]}")
        self.pos += 1
        return token
    
    def parse(self) -> Prop:
        result = self.parse_implication()
        if self.peek() is not None:
            token = self.peek()
            raise SyntaxError(f"Unexpected token {token[1]!r} at position {token[2]} after end of expression")
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
        if self.peek() and self.peek()[0] in ['NOT', 'BOTTOM']:
            token_type = self.peek()[0]
            self.consume(token_type)
            if token_type == 'BOTTOM':
                return bottom()
            else:
                prop = self.parse_not()
                return not_(prop)
        else:
            return self.parse_quantifier_or_atomic()
    
    def parse_quantifier_or_atomic(self) -> Prop:
        tok = self.peek()
        if tok and tok[0] == 'FORALL':
            self.consume('FORALL')
            var_token = self.consume('VAR')
            if self.peek() and self.peek()[0] == 'DOT':
                self.consume('DOT')
            body = self.parse_implication()
            return forall(var_token[1], body)
        elif tok and tok[0] == 'EXISTS':
            self.consume('EXISTS')
            var_token = self.consume('VAR')
            if self.peek() and self.peek()[0] == 'DOT':
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
            args = []
            if self.peek() and self.peek()[0] == 'LPAREN':
                self.consume('LPAREN')
                args = self.parse_term_list()
                self.consume('RPAREN')
            return pred(pred_name, args)
        elif tok[0] == 'VAR':
            var_name = self.consume('VAR')[1]
            return var(var_name)
        elif tok[0] == 'EQ':
            self.consume('EQ')
            # Handle equality
            left = self.parse_term()
            self.consume('EQ')  # Consume the second =
            right = self.parse_term()
            return eq(left, right)
        else:
            raise SyntaxError(f"Unexpected token {tok[1]!r} at position {tok[2]}")
    
    def parse_term_list(self) -> List[Term]:
        terms = []
        if self.peek() and self.peek()[0] != 'RPAREN':
            terms.append(self.parse_term())
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
                if self.peek() and self.peek()[0] == 'DOT':
                    break
            if self.peek() and self.peek()[0] == 'DOT':
                self.consume('DOT')
            body = self.parse_term()
            return ("lambda", params, body)
        elif tok[0] == 'LPAREN':
            self.consume('LPAREN')
            # Check if this is an application or just grouping
            first_term = self.parse_term()
            if self.peek() and self.peek()[0] != 'RPAREN':
                # It's an application
                second_term = self.parse_term()
                self.consume('RPAREN')
                return ("app", first_term, second_term)
            else:
                # Just grouping
                self.consume('RPAREN')
                return first_term
        else:
            raise SyntaxError(f"Unexpected token in term: {tok[1]!r} at position {tok[2]}")

def parse_formula(formula_str: str) -> Prop:
    """Parse a formula string into a Prop AST"""
    try:
        tokens = lex(formula_str)
        parser = Parser(tokens)
        return parser.parse()
    except Exception as e:
        # Provide more context for parsing errors
        raise ValueError(f"Parsing error: {str(e)}\nFormula: {formula_str}") from e

def parse_term(term_str: str) -> Term:
    """Parse a term string into a Term AST"""
    try:
        tokens = lex(term_str)
        parser = Parser(tokens)
        return parser.parse_term()
    except Exception as e:
        # Provide more context for parsing errors
        raise ValueError(f"Parsing error: {str(e)}\nTerm: {term_str}") from e

# === Export Functions for Each Proof Assistant ===
# Coq Export Functions
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
            args_str = ", ".join(term_to_coq(a) for a in args)
            return f"{name}({args_str})"
        case ('var', x): return x
        case ('const', c): return c.lower()  # Coq prefers lowercase identifiers
        case _: 
            logger.warning(f"Unhandled proposition type in Coq export: {prop}")
            return str(prop)

def term_to_coq(t: Term) -> str:
    match t:
        case ("var", x): return x
        case ("const", c): return c.lower()  # Coq prefers lowercase identifiers
        case ("fun", name, args):
            args_str = " ".join(term_to_coq(a) for a in args)
            return f"({name.lower()} {args_str})"
        case ("lambda", params, body):
            params_str = " ".join(params)
            return f"(fun {params_str} => {term_to_coq(body)})"
        case ("app", f, a): return f"({term_to_coq(f)} {term_to_coq(a)})"
        case _: 
            logger.warning(f"Unhandled term type in Coq export: {t}")
            return str(t)

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
        "not_intro": "intro",
        "not_elim": "apply NNPP",
        "auto": "auto",
        "forall_elim": "specialize",
        "dne": "apply NNPP"
    }
    base = mapping.get(tactic_name, tactic_name)
    if tactic_name == "intro" and arguments:
        return f"intros {arguments[0]}"
    elif tactic_name == "exact" and arguments:
        return f"exact {arguments[0]}"
    elif tactic_name == "destruct" and arguments:
        return f"destruct {arguments[0]}"
    elif tactic_name == "forall_elim" and len(arguments) >= 2:
        # arguments[0] is hyp name, arguments[1] is term
        return f"specialize ({arguments[0]} {term_to_coq(arguments[1])})"
    elif tactic_name == "exists_intro" and arguments:
        return f"exists {term_to_coq(arguments[0])}"
    elif tactic_name == "dne" and arguments:
        return f"apply NNPP in {arguments[0]}"
    return base

# Isabelle Export Functions
def prop_to_isabelle(prop: Prop) -> str:
    match prop:
        case ('not', p): return f"~({prop_to_isabelle(p)})"
        case ('and', p, q): return f"({prop_to_isabelle(p)} & {prop_to_isabelle(q)})"
        case ('or', p, q): return f"({prop_to_isabelle(p)} | {prop_to_isabelle(q)})"
        case ('implies', p, q): return f"({prop_to_isabelle(p)} --> {prop_to_isabelle(q)})"
        case ('forall', v, body): return f"(!{v}. {prop_to_isabelle(body)})"
        case ('exists', v, body): return f"(?{v}. {prop_to_isabelle(body)})"
        case ('bottom',): return "False"
        case ('pred', name, args):
            if name == "=" and len(args) == 2:
                return f"({term_to_isabelle(args[0])} = {term_to_isabelle(args[1])})"
            args_str = ", ".join(term_to_isabelle(a) for a in args)
            return f"{name}({args_str})"
        case ('var', x): return x
        case ('const', c): return c
        case _: 
            logger.warning(f"Unhandled proposition type in Isabelle export: {prop}")
            return str(prop)

def term_to_isabelle(t: Term) -> str:
    match t:
        case ("var", x): return x
        case ("const", c): return c
        case ("fun", name, args):
            if not args:
                return name
            args_str = ", ".join(term_to_isabelle(a) for a in args)
            return f"{name}({args_str})"
        case ("lambda", params, body):
            params_str = ", ".join(params)
            return f"%{params_str}. {term_to_isabelle(body)}"
        case ("app", f, a): 
            return f"{term_to_isabelle(f)} {term_to_isabelle(a)}"
        case _: 
            logger.warning(f"Unhandled term type in Isabelle export: {t}")
            return str(t)

def tactic_to_isabelle(tactic_name: str, arguments: List[Any]) -> str:
    mapping = {
        "intro": "assume",
        "exact": "then show",
        "split": "thus \"?thesis\" using assms by auto",
        "destruct": "have",
        "left": "thus \"?thesis\" by (rule disjI1)",
        "right": "thus \"?thesis\" by (rule disjI2)",
        "contradiction": "thus \"?thesis\" by contradiction",
        "assumption": "thus \"?thesis\" by assumption",
        "reflexivity": "thus \"?thesis\" by simp",
        "exists_intro": "thus \"?thesis\" by (rule exI)",
        "not_intro": "assume",
        "auto": "by auto"
    }
    base = mapping.get(tactic_name, f"(* {tactic_name} *)")
    if tactic_name == "intro" and arguments:
        return f"assume {arguments[0]}: \"{prop_to_isabelle(arguments[1])}\""
    elif tactic_name == "exact" and arguments:
        return f"then show \"{prop_to_isabelle(arguments[0])}\" ."
    elif tactic_name == "destruct":
        if len(arguments) >= 2:
            return f"have \"{prop_to_isabelle(arguments[1])}\" using {arguments[0]} by auto"
    return base

# Lean Export Functions
def prop_to_lean(prop: Prop) -> str:
    match prop:
        case ('not', p): return f"¬({prop_to_lean(p)})"
        case ('and', p, q): return f"({prop_to_lean(p)} ∧ {prop_to_lean(q)})"
        case ('or', p, q): return f"({prop_to_lean(p)} ∨ {prop_to_lean(q)})"
        case ('implies', p, q): return f"({prop_to_lean(p)} → {prop_to_lean(q)})"
        case ('forall', v, body): return f"(∀ {v}, {prop_to_lean(body)})"
        case ('exists', v, body): return f"(∃ {v}, {prop_to_lean(body)})"
        case ('bottom',): return "False"
        case ('pred', name, args):
            if name == "=" and len(args) == 2:
                return f"({term_to_lean(args[0])} = {term_to_lean(args[1])})"
            args_str = ", ".join(term_to_lean(a) for a in args)
            return f"{name}({args_str})"
        case ('var', x): return x
        case ('const', c): return c
        case _: 
            logger.warning(f"Unhandled proposition type in Lean export: {prop}")
            return str(prop)

def term_to_lean(t: Term) -> str:
    match t:
        case ("var", x): return x
        case ("const", c): return c
        case ("fun", name, args):
            if not args:
                return name
            args_str = " ".join(term_to_lean(a) for a in args)
            return f"{name} {args_str}"
        case ("lambda", params, body):
            params_str = " ".join(params)
            return f"fun {params_str} => {term_to_lean(body)}"
        case ("app", f, a): 
            return f"({term_to_lean(f)} {term_to_lean(a)})"
        case _: 
            logger.warning(f"Unhandled term type in Lean export: {t}")
            return str(t)

def tactic_to_lean(tactic_name: str, arguments: List[Any]) -> str:
    mapping = {
        "intro": "intro",
        "exact": "exact",
        "split": "constructor",
        "left": "left",
        "right": "right",
        "destruct": "cases",
        "contradiction": "contradiction",
        "assumption": "assumption",
        "reflexivity": "reflexivity",
        "exists_intro": "use",
        "not_intro": "intro",
        "not_elim": "by_contra",
        "auto": "aesop",
        "forall_elim": "specialize",
        "dne": "by_contra"
    }
    base = mapping.get(tactic_name, tactic_name)
    if tactic_name == "intro" and arguments:
        return f"intro {arguments[0]}"
    elif tactic_name == "exact" and arguments:
        return f"exact {arguments[0]}"
    elif tactic_name == "destruct" and arguments:
        return f"cases {arguments[0]}"
    elif tactic_name == "forall_elim" and len(arguments) >= 2:
        # arguments[0] is hyp name, arguments[1] is term
        return f"specialize {arguments[0]} {term_to_lean(arguments[1])}"
    elif tactic_name == "exists_intro" and arguments:
        return f"use {term_to_lean(arguments[0])}"
    elif tactic_name == "dne" and arguments:
        return f"by_contra! {arguments[0]}"
    return base

# === Command Processing with Enhanced Features ===
def explain_tactic(tactic_name: str) -> str:
    explanations = {
        "intro": "Introduces an implication or universal quantifier. For A → B, it assumes A and proves B. For ∀x. P(x), it introduces a fresh variable.",
        "exact": "Solves the goal when it exactly matches a hypothesis or formula.",
        "split": "Splits a conjunction goal A ∧ B into two subgoals: prove A and prove B.",
        "destruct": "Performs case analysis on a disjunction or conjunction hypothesis.",
        "left": "Solves a disjunction goal A ∨ B by proving A.",
        "right": "Solves a disjunction goal A ∨ B by proving B.",
        "forall_elim": "Instantiates a universal quantifier ∀x. P(x) with a specific term t to get P(t).",
        "exists_intro": "Provides a witness t for an existential quantifier goal ∃x. P(x) to get P(t).",
        "contradiction": "Solves the goal when a contradiction (P and ¬P or ⊥) is in the context.",
        "assume": "Adds a new hypothesis to the context.",
        "rename": "Renames a hypothesis.",
        "clear": "Removes a hypothesis from the context.",
        "not_intro": "Proves ¬P by assuming P and proving ⊥.",
        "assumption": "Solves the goal if it matches a hypothesis in the context.",
        "reflexivity": "Solves equality goals of the form t = t.",
        "auto": "Attempts to automatically prove the goal using simple tactics.",
        "undo": "Undoes the last tactic application.",
        "redo": "Redoes the last undone tactic application.",
        "save": "Saves the current proof state to a file.",
        "load": "Loads a proof state from a file.",
        "export": "Exports the proof to various theorem provers (Coq, Isabelle, Lean).",
        "hint": "Provides hints for the current goal."
    }
    return explanations.get(tactic_name, "No explanation available.")

def tactic_hint(state: ProofState) -> None:
    """Provide hints for the current goal"""
    current = state.current()
    if current is None:
        print("No current goal")
        return
    
    ctx, goal = current
    print(f"\nCurrent goal: {prop_repr(goal)}")
    print("Possible next steps:")
    
    # Analyze goal structure
    match goal:
        case ('implies', p, q):
            print("- Use 'intro [name]' to assume the premise")
            print("- Look for hypotheses that might help prove the conclusion")
        case ('and', p, q):
            print("- Use 'split' to break into two subgoals")
        case ('forall', v, body):
            print("- Use 'intro' to introduce a new variable")
        case ('exists', v, body):
            print("- Use 'exists_intro <term>' to provide a witness")
            print("  Example: exists_intro x or exists_intro (f a)")
        case ('or', p, q):
            print("- Use 'left' to prove the left disjunct")
            print("- Use 'right' to prove the right disjunct")
        case ('not', p):
            print("- Use 'not_intro [name]' to assume the negation and prove ⊥")
        case ('pred', "=", [left, right]) if term_eq(left, right):
            print("- Use 'reflexivity' to solve the equality")
        case ('bottom',):
            print("- Look for contradictory hypotheses (P and ¬P)")
            print("- Use 'contradiction' if you have a direct contradiction")
        case _:
            print("- Try 'assumption' if goal matches a hypothesis")
            print("- Try 'auto' for automatic proof search")
    
    # Analyze context for useful hypotheses
    if ctx:
        print("\nRelevant hypotheses:")
        for name, hyp in ctx:
            match hyp:
                case ('implies', A, B) if alpha_eq(B, goal):
                    print(f"- {name} : {prop_repr(hyp)}  (can be used with 'exact {name}' if you prove {prop_repr(A)})")
                case ('and', A, B):
                    print(f"- {name} : {prop_repr(hyp)}  (use 'destruct {name}' to get {A} and {B} separately)")
                case ('or', A, B):
                    print(f"- {name} : {prop_repr(hyp)}  (use 'destruct {name}' for case analysis)")
                case ('not', ('not', P)) if alpha_eq(P, goal):
                    print(f"- {name} : {prop_repr(hyp)}  (use 'dne {name}' for double negation elimination)")
                case ('forall', v, body):
                    print(f"- {name} : {prop_repr(hyp)}  (use 'forall_elim {name} <term>' to instantiate)")
    else:
        print("\nContext is empty. You may need to use 'assume <formula>' to add hypotheses.")

def process_command(state: Optional[ProofState], command: str) -> Optional[ProofState]:
    cmd = command.strip()
    if not cmd:
        return state
    
    parts = cmd.split(maxsplit=1)
    cmd_name = parts[0].lower()
    arg = parts[1] if len(parts) > 1 else None
    
    try:
        # Export commands
        if cmd_name == "export":
            if state is None:
                print("No active proof to export.")
                return state
            if not state.proof_tree.initial_goal:
                print("No initial goal set. Use 'goal' command first.")
                return state
            
            # Set theorem name if not already set
            if state.proof_tree.theorem_name == "theorem":
                theorem_name = input("Enter theorem name (default: theorem): ").strip() or "theorem"
                state.proof_tree.theorem_name = theorem_name
            
            export_parts = arg.split() if arg else ["all"]
            system = export_parts[0].lower()
            directory = export_parts[1] if len(export_parts) > 1 else "."
            
            try:
                if system == "all":
                    exports = state.proof_tree.export_all(directory)
                    print("Exported to all theorem provers:")
                    for system, code in exports.items():
                        if code:
                            print(f"  - {system.upper()}: {len(code.splitlines())} lines")
                elif system == "coq":
                    code = state.proof_tree.export_coq()
                    if code:
                        print("Coq export:")
                        print(code)
                elif system == "isabelle":
                    code = state.proof_tree.export_isabelle()
                    if code:
                        print("Isabelle export:")
                        print(code)
                elif system == "lean":
                    code = state.proof_tree.export_lean()
                    if code:
                        print("Lean export:")
                        print(code)
                else:
                    print(f"Unknown proof system: {system}. Supported systems: coq, isabelle, lean, all")
            except Exception as e:
                print(f"Export error: {e}")
                logger.exception("Export failed")
            return state
        
        # Save/Load proof state
        elif cmd_name == "save":
            if state is None:
                print("No active proof to save.")
                return state
            filename = arg or f"proof_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
            try:
                state.proof_tree.save_proof_state(filename)
                print(f"Proof state saved to {filename}")
            except Exception as e:
                print(f"Error saving proof state: {e}")
                logger.exception("Save failed")
            return state
        
        elif cmd_name == "load":
            if not arg:
                print("Usage: load <filename>")
                return state
            try:
                # Create a new proof tree and load state
                new_tree = ProofTree()
                new_tree.load_proof_state(arg)
                
                # Reconstruct initial state
                if new_tree.initial_goal:
                    new_state = ProofState([new_tree.initial_goal], new_tree)
                    print(f"Proof state loaded from {arg}")
                    print(f"Theorem name: {new_tree.theorem_name}")
                    print(f"Initial goal: {prop_repr(new_tree.initial_goal[1])}")
                    print(f"Steps loaded: {len(new_tree.steps)}")
                    
                    # If there are steps, we need to replay them to get the current state
                    if new_tree.steps:
                        print("\nReplaying proof steps...")
                        current_state = new_state
                        for i, step in enumerate(new_tree.steps, 1):
                            print(f"Step {i}/{len(new_tree.steps)}: {step.tactic_name} {step.arguments}")
                            try:
                                # This is a bit tricky - we need to apply each tactic
                                # We'll use a simplified approach that might not perfectly
                                # reproduce all states, but will get us close
                                tactic_name = step.tactic_name
                                args = step.arguments
                                
                                if tactic_name == "intro":
                                    name = args[0] if args else None
                                    current_state = tactic_intro(current_state, name)
                                elif tactic_name == "exact":
                                    term = args[0] if args else ""
                                    current_state = tactic_exact(current_state, term)
                                elif tactic_name == "split":
                                    current_state = tactic_split(current_state)
                                elif tactic_name == "destruct":
                                    name = args[0] if args else ""
                                    current_state = tactic_destruct(current_state, name)
                                elif tactic_name == "left":
                                    current_state = tactic_left(current_state)
                                elif tactic_name == "right":
                                    current_state = tactic_right(current_state)
                                # Add other tactics as needed
                                
                                print(f"  Remaining goals: {len(current_state.goals)}")
                            except Exception as e:
                                print(f"  Error replaying step: {e}")
                                break
                        
                        # Use the final state after replaying steps
                        return current_state
                    else:
                        return new_state
                else:
                    print("No initial goal found in saved state")
            except Exception as e:
                print(f"Error loading proof state: {e}")
                logger.exception("Load failed")
            return state
        
        # Undo/Redo
        elif cmd_name == "undo":
            if state is None:
                print("No active proof.")
                return state
            new_state = state.undo()
            if new_state:
                print("Undo successful")
                return new_state
            else:
                print("Nothing to undo")
                return state
        
        elif cmd_name == "redo":
            if state is None:
                print("No active proof.")
                return state
            new_state = state.redo()
            if new_state:
                print("Redo successful")
                return new_state
            else:
                print("Nothing to redo")
                return state
        
        # Core proof commands
        elif cmd_name == "help":
            print_help()
            return state
        
        elif cmd_name == "goal":
            if arg is None:
                print("Usage: goal <expr>")
                return state
            try:
                prop = parse_formula(arg)
                theorem_name = input("Enter theorem name (default: theorem): ").strip() or "theorem"
                new_state = ProofState([([], prop)])
                new_state.proof_tree.set_initial_goal(([], prop), theorem_name)
                print(f"\nGoal set: {prop_repr(prop)}")
                print(f"Theorem name: {theorem_name}")
                return new_state
            except Exception as e:
                print(f"Parsing error: {e}")
                logger.exception("Goal parsing failed")
                return state
        
        elif cmd_name == "intro":
            name = arg if arg else None
            return tactic_intro(state, name)
        
        elif cmd_name == "exact":
            if arg is None:
                print("Usage: exact <hyp_name> or exact <formula>")
                return state
            # First try to interpret as hypothesis name
            try:
                # Check if it's a hypothesis name by looking in context
                current = state.current()
                if current:
                    ctx, _ = current
                    hyp_names = [n for n, _ in ctx]
                    if arg in hyp_names:
                        return tactic_exact(state, arg)
            except:
                pass
            
            # If not a hypothesis name, try to parse as formula
            try:
                prop = parse_formula(arg)
                return tactic_exact(state, prop)
            except Exception as e:
                print(f"Error parsing formula: {e}")
                # Try as hypothesis name anyway
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
            return tactic_forall_elim(state, hyp_name, term_str)
        
        elif cmd_name == "exists_intro":
            if arg is None:
                print("Usage: exists_intro <term>")
                return state
            return tactic_exists_intro(state, arg)
        
        elif cmd_name == "contradiction":
            return tactic_contradiction(state)
        
        elif cmd_name == "assume":
            if arg is None:
                print("Usage: assume <formula>")
                return state
            return tactic_assume(state, arg)
        
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
        
        elif cmd_name == "assumption":
            return tactic_assumption(state)
        
        elif cmd_name == "reflexivity":
            return tactic_reflexivity(state)
        
        elif cmd_name == "auto":
            depth = int(arg) if arg and arg.isdigit() else 3
            return tactic_auto(state, depth)
        
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
                print("Context:")
                for i, (name, prop) in enumerate(ctx):
                    print(f"{i}: {name} : {prop_repr(prop)}")
            return state
        
        elif cmd_name == "explain":
            if arg is None:
                print("Usage: explain <tactic_name>")
                return state
            print(explain_tactic(arg))
            return state
        
        elif cmd_name == "proof":
            state.proof_tree.pretty_print()
            return state
        
        elif cmd_name == "hint":
            tactic_hint(state)
            return state
        
        elif cmd_name == "exit":
            print("Exiting.")
            sys.exit(0)
        
        else:
            print(f"Unknown command: {cmd_name}")
            print("Type 'help' for available commands")
            return state
    
    except Exception as e:
        print(f"Error: {e}")
        logger.exception(f"Command '{cmd}' failed")
        return state

def print_help():
    print("""🔍 Advanced Proof Assistant with Multi-Prover Export
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
  assumption                    Solve if goal matches hypothesis
  reflexivity                   Solve t = t
  auto [depth]                  Automatic proof search
Proof management:
  state                         Show current proof state
  context                       Show context with indices
  undo                          Undo last tactic
  redo                          Redo last undone tactic
  hint                          Get proof hints
  explain <tactic>              Explain a tactic
  proof                         Show proof steps
  save <filename>               Save proof state
  load <filename>               Load proof state
Export commands:
  export coq [dir]              Export to Coq (default: current directory)
  export isabelle [dir]         Export to Isabelle/HOL
  export lean [dir]             Export to Lean 4
  export all [dir]              Export to all supported provers
Other commands:
  help                          Show this help
  exit                          Quit
""")

# === REPL and Main ===
def repl():
    print("🔍 Advanced Proof Assistant with Multi-Prover Export")
    print("Type 'help' for commands, 'exit' to quit.")
    
    # Setup readline for history and tab completion
    history_file = os.path.expanduser("~/.proof_assistant_history")
    try:
        readline.read_history_file(history_file)
    except FileNotFoundError:
        pass
    
    # Define tab completion
    def completer(text, state):
        commands = [
            "goal", "intro", "exact", "split", "destruct", "left", "right",
            "forall_elim", "exists_intro", "contradiction", "assume", "rename",
            "clear", "not_intro", "assumption", "reflexivity", "auto", "state",
            "context", "hint", "explain", "proof", "undo", "redo", "save", "load",
            "export", "help", "exit"
        ]
        matches = [cmd for cmd in commands if cmd.startswith(text)]
        if state < len(matches):
            return matches[state]
        return None
    
    readline.set_completer(completer)
    readline.parse_and_bind("tab: complete")
    
    state: Optional[ProofState] = None
    while True:
        try:
            prompt = "proof> " if state is None or not state.is_complete() else "completed> "
            cmd = input(prompt).strip()
            
            # Skip empty commands
            if not cmd:
                continue
            
            # Save to history
            readline.add_history(cmd)
            
            # Process command
            old_state = state
            state = process_command(state, cmd)
            
            # Show state after successful command (unless it's a query command)
            if state and state != old_state and cmd.split()[0] not in ["state", "context", "hint", "explain", "proof"]:
                if state.is_complete():
                    print("\n✅ Proof complete!")
                    print("Proof summary:")
                    state.proof_tree.pretty_print()
                    print("\nUse 'export <system>' to export to a theorem prover")
                else:
                    print("\n" + str(state))
        
        except (EOFError, KeyboardInterrupt):
            print("\nUse 'exit' to quit")
        except Exception as e:
            print(f"Unexpected error: {e}")
            logger.exception("Unexpected error in REPL")

def run_proof_file(filename: str, step_by_step: bool = False):
    """Run proof commands from a file"""
    print(f"Running proof script: {filename}")
    state: Optional[ProofState] = None
    
    try:
        with open(filename, 'r', encoding='utf-8') as f:
            for lineno, line in enumerate(f, 1):
                cmd = line.strip()
                # Skip comments and empty lines
                if not cmd or cmd.startswith('#'):
                    continue
                
                print(f"\nLine {lineno}: {cmd}")
                state = process_command(state, cmd)
                
                if state and state.is_complete():
                    print("\nProof complete!")
                    break
                
                if step_by_step and state:
                    print("\nCurrent state:")
                    print(state)
                    input("Press Enter to continue...")
    
    except FileNotFoundError:
        print(f"Error: File not found: {filename}")
        return
    except Exception as e:
        print(f"Error executing proof script: {e}")
        logger.exception(f"Error in proof file {filename}")
        return
    
    print("\n----- End of proof script -----")
    if state and not state.is_complete():
        print("Warning: Proof not completed!")

def run_proofs_in_folder(folder_path: str):
    """Run all proof files in a folder"""
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
    logger.info("Proof Assistant started")
    
    # Save history on exit
    import atexit
    history_file = os.path.expanduser("~/.proof_assistant_history")
    atexit.register(lambda: readline.write_history_file(history_file))
    
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
            sys.exit(1)
    elif len(sys.argv) == 3 and sys.argv[1] == "--step":
        run_proof_file(sys.argv[2], step_by_step=True)
    else:
        print(f"Usage: {sys.argv[0]} [--step] [prooffile|proofs_folder]")
        sys.exit(1)
    
    logger.info("Proof Assistant exited")

if __name__ == "__main__":
    main()