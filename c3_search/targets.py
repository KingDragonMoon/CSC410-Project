from collections.abc import Iterator
from dataclasses import dataclass
from itertools import chain
from typing import Literal

from c1_checker.axioms import instantiate_axiom
from c1_checker.checker import ProofLine
from c3_search.initialization import (
    CORE_AXIOM_ARITIES,
    _iter_conjuncts,
    match_axiom_antecedent,
    match_axiom_conjuncts,
    match_axiom_conclusion,
)
from ltl.formula import Always, And, Formula, Iff, Implies, Not, Or


@dataclass(frozen=True)
class Strategy:
    premises: tuple[Formula, ...]
    rule: Literal["R1", "R2", "R3"]
    axiom: ProofLine | None = None


def target_strategies(goal: Formula) -> Iterator[Strategy]:
    for axiom_name, _ in CORE_AXIOM_ARITIES:
        substitution = match_axiom_conclusion(axiom_name, goal)
        if substitution is not None:
            instance = instantiate_axiom(axiom_name, *substitution)
            yield Strategy(
                premises=(instance.left,),
                rule="R2",
                axiom=ProofLine(instance, axiom_name, substitution=substitution),
            )

    if isinstance(goal, Implies):
        seen_instances: set[Formula] = set()
        for antecedent in chain((goal.left,), _iter_conjuncts(goal.left)):
            for axiom_name, _ in CORE_AXIOM_ARITIES:
                substitution = match_axiom_antecedent(axiom_name, antecedent)
                if substitution is not None:
                    instance = instantiate_axiom(axiom_name, *substitution)
                    if instance not in seen_instances:
                        seen_instances.add(instance)
                        yield Strategy((instance,), "R1")

    if isinstance(goal, Always):
        yield Strategy((goal.body,), "R3")
    elif isinstance(goal, And):
        yield Strategy((goal.left, goal.right), "R1")
    elif isinstance(goal, Or):
        yield Strategy((goal.left,), "R1")
        yield Strategy((goal.right,), "R1")
    elif isinstance(goal, Implies):
        if isinstance(goal.right, And):
            yield Strategy(
                (Implies(goal.left, goal.right.left), Implies(goal.left, goal.right.right)),
                "R1",
            )
        yield Strategy((Not(goal.left),), "R1")
        yield Strategy((goal.right,), "R1")
    elif isinstance(goal, Iff):
        yield Strategy((Implies(goal.left, goal.right), Implies(goal.right, goal.left)), "R1")

    for axiom_name, _ in CORE_AXIOM_ARITIES:
        for substitution in match_axiom_conjuncts(axiom_name, goal):
            instance = instantiate_axiom(axiom_name, *substitution)
            yield Strategy(
                premises=(instance.left,),
                rule="R2",
                axiom=ProofLine(instance, axiom_name, substitution=substitution),
            )
