from collections.abc import Iterable, Iterator
from dataclasses import dataclass

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


@dataclass(frozen=True)
class _Placeholder(Formula):
    name: str


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
    candidates = list(_iter_subformulas(goal))
    for candidate in extra_candidates:
        tuple(_iter_subformulas(candidate))
        candidates.append(candidate)
    return tuple(dict.fromkeys(candidates))


def _match_pattern(
    pattern: Formula, formula: Formula, bindings: dict[str, Formula]
) -> bool:
    if isinstance(pattern, _Placeholder):
        if pattern.name in bindings:
            return bindings[pattern.name] == formula
        bindings[pattern.name] = formula
        return True
    if type(pattern) is not type(formula):
        return False
    if isinstance(pattern, Atom):
        return pattern == formula
    if isinstance(pattern, (Not, Next, Always, Eventually)):
        return _match_pattern(pattern.body, formula.body, bindings)
    if isinstance(pattern, (And, Or, Implies, Iff)):
        return (
            _match_pattern(pattern.left, formula.left, bindings)
            and _match_pattern(pattern.right, formula.right, bindings)
        )
    return False


def _axiom_pattern(axiom_name: str) -> tuple[tuple[_Placeholder, ...], Formula]:
    arity = dict(CORE_AXIOM_ARITIES).get(axiom_name)
    if arity is None:
        raise ValueError()
    placeholders = tuple(_Placeholder(name) for name in ("p", "q")[:arity])
    return placeholders, instantiate_axiom(axiom_name, *placeholders)


def match_axiom(axiom_name: str, goal: Formula) -> tuple[Formula, ...] | None:
    placeholders, pattern = _axiom_pattern(axiom_name)
    tuple(_iter_subformulas(goal))
    bindings: dict[str, Formula] = {}
    if not _match_pattern(pattern, goal, bindings):
        return None
    return tuple(bindings[placeholder.name] for placeholder in placeholders)


def match_axiom_conclusion(axiom_name: str, goal: Formula) -> tuple[Formula, ...] | None:
    placeholders, pattern = _axiom_pattern(axiom_name)
    tuple(_iter_subformulas(goal))
    if not isinstance(pattern, Implies):
        return None
    bindings: dict[str, Formula] = {}
    if not _match_pattern(pattern.right, goal, bindings):
        return None
    if any(placeholder.name not in bindings for placeholder in placeholders):
        return None
    return tuple(bindings[placeholder.name] for placeholder in placeholders)


def match_axiom_antecedent(axiom_name: str, antecedent: Formula) -> tuple[Formula, ...] | None:
    placeholders, pattern = _axiom_pattern(axiom_name)
    tuple(_iter_subformulas(antecedent))
    if not isinstance(pattern, Implies):
        return None
    bindings: dict[str, Formula] = {}
    if not _match_pattern(pattern.left, antecedent, bindings):
        return None
    if any(placeholder.name not in bindings for placeholder in placeholders):
        return None
    return tuple(bindings[placeholder.name] for placeholder in placeholders)


def _iter_conjuncts(formula: Formula) -> Iterator[Formula]:
    if isinstance(formula, And):
        for conjunct in (formula.left, formula.right):
            yield conjunct
            yield from _iter_conjuncts(conjunct)


def match_axiom_conjuncts(axiom_name: str, goal: Formula) -> Iterator[tuple[Formula, ...]]:
    placeholders, pattern = _axiom_pattern(axiom_name)
    tuple(_iter_subformulas(goal))
    if not isinstance(pattern, Implies):
        return
    conjuncts = sorted(
        _iter_conjuncts(pattern.right),
        key=lambda formula: isinstance(formula, _Placeholder),
    )
    seen: set[tuple[Formula, ...]] = set()
    for conjunct in conjuncts:
        bindings: dict[str, Formula] = {}
        if not _match_pattern(conjunct, goal, bindings):
            continue
        if any(placeholder.name not in bindings for placeholder in placeholders):
            continue
        substitution = tuple(bindings[placeholder.name] for placeholder in placeholders)
        if substitution not in seen:
            seen.add(substitution)
            yield substitution


def initialize_axioms(goals: Iterable[Formula]) -> list[ProofLine]:
    proof_lines = []
    for goal in dict.fromkeys(goals):
        for axiom_name, _ in CORE_AXIOM_ARITIES:
            substitution = match_axiom(axiom_name, goal)
            if substitution is None:
                continue
            proof_lines.append(
                ProofLine(
                    formula=instantiate_axiom(axiom_name, *substitution),
                    rule=axiom_name,
                    substitution=substitution,
                )
            )
            break
    return proof_lines
