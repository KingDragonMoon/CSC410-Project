from collections.abc import Iterable, Iterator
from itertools import product

from c1_checker.axioms import instantiate_axiom
from c1_checker.checker import ProofLine
from ltl.formula import (
    Always,
    And,
    Atom,
    Eventually,
    Formula,
    Iff,
    Implies,
    Next,
    Not,
    Or,
)


CORE_AXIOM_ARITIES = (
    ("A1", 1),
    ("A2", 2),
    ("A3", 1),
    ("A4", 2),
    ("A5", 1),
    ("A6", 1),
)


def _iter_subformulas(formula: Formula) -> Iterator[Formula]:
    formula_type = type(formula)
    if formula_type is Atom:
        if type(formula.name) is not str:
            raise TypeError("An atom's name must be a string.")
        children = ()
    elif formula_type in (Not, Next, Always, Eventually):
        children = (formula.body,)
    elif formula_type in (And, Or, Implies, Iff):
        children = (formula.left, formula.right)
    else:
        raise TypeError(f"Unsupported formula in the core fragment: {formula_type.__name__}")

    yield formula
    for child in children:
        yield from _iter_subformulas(child)


def collect_candidates(
    goal: Formula, extra_candidates: Iterable[Formula] = ()
) -> tuple[Formula, ...]:
    """Freeze distinct goal subformulas in preorder, followed by explicit extras.

    The goal itself is included. Extras are added as whole formulas, without
    automatically adding their subformulas. Weak until is unsupported.
    """
    candidates = list(_iter_subformulas(goal))
    for candidate in extra_candidates:
        tuple(_iter_subformulas(candidate))
        candidates.append(candidate)
    return tuple(dict.fromkeys(candidates))


def initialize_axioms(candidate_pool: Iterable[Formula]) -> list[ProofLine]:
    """Instantiate A1–A6 over a fixed pool, with no inference-rule expansion.

    For n distinct candidates this produces 4*n + 2*n*n lines. Both orders
    of each pair and pairs containing the same candidate are included.
    """
    candidates = tuple(dict.fromkeys(candidate_pool))
    for candidate in candidates:
        tuple(_iter_subformulas(candidate))

    proof_lines = []
    for axiom_name, arity in CORE_AXIOM_ARITIES:
        for substitution in product(candidates, repeat=arity):
            proof_lines.append(
                ProofLine(
                    formula=instantiate_axiom(axiom_name, *substitution),
                    rule=axiom_name,
                    substitution=substitution,
                )
            )
    return proof_lines
