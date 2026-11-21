from dataclasses import dataclass
from z3 import Z3Exception

from ltl.formula import Always, And, Atom, Eventually, Formula, Iff, Implies, Next, Not, Or, WeakUntil
from c2_propositional.backend import check_tautology
from c1_checker.axioms import AXIOMS, instantiate_axiom


@dataclass(frozen=True)
class ProofLine:
    formula: Formula
    rule: str                               # justification (A1, R1, etc)
    refs: tuple[int, ...] = ()              # indices of earlier lines used in the justification
    substitution: tuple[Formula, ...] = ()  # formulas substituted for an axioms p and q

#Checks to see if the formula is well-formed
def _is_formula(formula) -> bool:
    kind = type(formula)
    if kind is Atom:
        return type(formula.name) is str
    if kind in (Not, Next, Always, Eventually):
        return _is_formula(formula.body)
    if kind in (And, Or, Implies, Iff, WeakUntil):
        return _is_formula(formula.left) and _is_formula(formula.right)
    return False


def check_proof(goal: Formula, proof: list[ProofLine]) -> bool:
    """References are zero-based and strictly earlier. Errors mean rejection."""
    try:
        # reject empty proofs, non-list proofs, and non-formula goals
        if type(proof) is not list or not proof or not _is_formula(goal):
            return False
    
        for index, line in enumerate(proof):

            # First, verify that the fields and substitutions of the line are well-formed. If not, reject the proof.
            if type(line) is not ProofLine or not _is_formula(line.formula):
                return False
            if type(line.rule) is not str or type(line.refs) is not tuple or type(line.substitution) is not tuple:
                return False
            if any(type(ref) is not int or not 0 <= ref < index for ref in line.refs):
                return False
            if not all(_is_formula(value) for value in line.substitution):
                return False

            # Next, verify that the line is justified by its rule and references. If not, reject the proof.
            if line.rule in AXIOMS:
                if line.refs or line.formula != instantiate_axiom(line.rule, *line.substitution):
                    return False
            elif line.rule == "R1":
                if line.refs or line.substitution or check_tautology(line.formula) is not True:
                    return False
            elif line.rule == "R2":
                # check that the line is justified by R2, which requires two references and no substitutions. 
                # The first reference should be an implication, and the second reference should be the antecedent. 
                # The formula of the current line should be the consequent of that implication.
                if len(line.refs) != 2 or line.substitution:
                    return False
                implication = proof[line.refs[0]].formula
                antecedent = proof[line.refs[1]].formula
                if implication != Implies(antecedent, line.formula):
                    return False
            elif line.rule == "R3":
                if len(line.refs) != 1 or line.substitution:
                    return False
                if line.formula != Always(proof[line.refs[0]].formula):
                    return False
            else:
                return False

        # Finally, verify that the last line of the proof is the goal formula. If not, reject the proof.
        return proof[-1].formula == goal
    except (TypeError, ValueError, AttributeError, IndexError, RecursionError, Z3Exception):
        return False
