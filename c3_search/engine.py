from collections import deque
from dataclasses import dataclass, fields

from c1_checker.checker import ProofLine, check_proof
from c2_propositional.backend import check_tautology
from c3_search.initialization import _iter_subformulas, initialize_axioms
from c3_search.targets import Strategy, target_strategies
from ltl.formula import Formula, Implies


@dataclass(frozen=True)
class SearchLimits:
    max_depth: int = 16
    max_formula_size: int = 128
    max_steps: int = 1000
    max_proof_lines: int = 256

    def __post_init__(self) -> None:
        for setting in fields(self):
            value = getattr(self, setting.name)
            minimum = 0 if setting.name == "max_depth" else 1
            if type(value) is not int or value < minimum:
                raise ValueError()


@dataclass(frozen=True)
class SearchResult:
    proof: list[ProofLine] | None
    reason: str
    steps: int
    targets_seen: int
    r1_checks: int
    limits_hit: tuple[str, ...]

    @property
    def proved(self) -> bool:
        return self.proof is not None


@dataclass(frozen=True)
class _Derivation:
    formula: Formula
    rule: str
    premises: tuple["_Derivation", ...] = ()
    substitution: tuple[Formula, ...] = ()


def _implication_chain(goal: Formula, premises: tuple[Formula, ...]) -> Formula:
    conclusion = goal
    for premise in reversed(premises):
        conclusion = Implies(premise, conclusion)
    return conclusion


class _Search:
    def __init__(self, limits: SearchLimits):
        self.limits = limits
        self.steps = 0
        self.r1_checks = 0
        self.targets: set[Formula] = set()
        self.active: set[Formula] = set()
        self.proved: dict[Formula, _Derivation] = {}
        self.implications_by_antecedent: dict[Formula, list[_Derivation]] = {}
        self.pending_facts: deque[_Derivation] = deque()
        self.propagating = False
        self.tautologies: dict[Formula, bool | None] = {}
        self.sizes: dict[Formula, int] = {}
        self.limits_hit: set[str] = set()

    def _fits(self, formula: Formula) -> bool:
        if formula not in self.sizes:
            self.sizes[formula] = sum(1 for _ in _iter_subformulas(formula))
        if self.sizes[formula] > self.limits.max_formula_size:
            self.limits_hit.add("max_formula_size")
            return False
        return True

    def _spend_step(self) -> bool:
        if self.steps >= self.limits.max_steps:
            self.limits_hit.add("max_steps")
            return False
        self.steps += 1
        return True

    def _is_tautology(self, formula: Formula) -> bool:
        if formula in self.tautologies:
            return self.tautologies[formula] is True
        if not self._spend_step():
            return False
        self.r1_checks += 1
        verdict = check_tautology(formula)
        self.tautologies[formula] = verdict
        return verdict is True

    def _remember(
        self,
        formula: Formula,
        rule: str,
        premises: tuple[_Derivation, ...] = (),
        substitution: tuple[Formula, ...] = (),
    ) -> _Derivation | None:
        if formula in self.proved:
            return self.proved[formula]
        if not self._fits(formula):
            return None
        derivation = _Derivation(formula, rule, premises, substitution)
        needed: set[Formula] = set()
        pending = [derivation]
        while pending:
            current = pending.pop()
            if current.formula in needed:
                continue
            needed.add(current.formula)
            if len(needed) > self.limits.max_proof_lines:
                self.limits_hit.add("max_proof_lines")
                return None
            pending.extend(current.premises)
        self.proved[formula] = derivation
        if isinstance(formula, Implies):
            self.implications_by_antecedent.setdefault(formula.left, []).append(derivation)
        self.pending_facts.append(derivation)
        self._propagate_r2()
        return derivation

    def _propagate_r2(self) -> None:
        if self.propagating:
            return
        self.propagating = True
        try:
            while self.pending_facts:
                fact = self.pending_facts.popleft()
                matches = [
                    (implication, fact)
                    for implication in self.implications_by_antecedent.get(fact.formula, ())
                ]
                if isinstance(fact.formula, Implies):
                    antecedent = self.proved.get(fact.formula.left)
                    if antecedent is not None:
                        matches.append((fact, antecedent))
                for implication, antecedent in matches:
                    conclusion = implication.formula.right
                    if conclusion in self.proved:
                        continue
                    if not self._spend_step():
                        self.pending_facts.clear()
                        return
                    self._remember(conclusion, "R2", (implication, antecedent))
        finally:
            self.propagating = False

    def _from_known_implications(self, goal: Formula) -> _Derivation | None:
        if isinstance(goal, Implies):
            implications = tuple(self.implications_by_antecedent.get(goal.left, ()))
            for implication in implications:
                proof = self._combine(goal, (implication,))
                if proof is not None:
                    return proof
        return None

    def _combine(self, goal: Formula, premises: tuple[_Derivation, ...]) -> _Derivation | None:
        implication = _implication_chain(goal, tuple(premise.formula for premise in premises))
        if not self._fits(implication) or not self._is_tautology(implication):
            return None
        current = self._remember(implication, "R1")
        for premise in premises:
            if current is None:
                return None
            current = self._remember(current.formula.right, "R2", (current, premise))
        return current

    def _try_strategy(self, goal: Formula, strategy: Strategy, depth: int) -> _Derivation | None:
        if depth >= self.limits.max_depth:
            self.limits_hit.add("max_depth")
            return None
        prerequisites = tuple(dict.fromkeys(strategy.premises))
        if strategy.axiom is not None and not self._fits(strategy.axiom.formula):
            return None
        if strategy.rule == "R1" and not self._fits(_implication_chain(goal, prerequisites)):
            return None
        projected_implication = None
        if (
            strategy.rule == "R2"
            and strategy.axiom is not None
            and strategy.axiom.formula.right != goal
        ):
            axiom = strategy.axiom
            implication = Implies(axiom.formula.left, goal)
            bridge = Implies(axiom.formula, implication)
            if not self._fits(bridge) or not self._is_tautology(bridge):
                return None
            axiom_proof = self._remember(axiom.formula, axiom.rule, substitution=axiom.substitution)
            if axiom_proof is None:
                return None
            projected_implication = self._combine(implication, (axiom_proof,))
            if projected_implication is None:
                return None
        subproofs = []
        for prerequisite in prerequisites:
            subproof = self._prove(prerequisite, depth + 1)
            if subproof is None:
                return None
            subproofs.append(subproof)

        if strategy.rule == "R1":
            return self._combine(goal, tuple(subproofs))
        if strategy.rule == "R3":
            return self._remember(goal, "R3", tuple(subproofs))
        if projected_implication is not None:
            return self._remember(goal, "R2", (projected_implication, subproofs[0]))
        axiom = strategy.axiom
        if axiom is None:
            raise RuntimeError()
        axiom_proof = self._remember(axiom.formula, axiom.rule, substitution=axiom.substitution)
        if axiom_proof is None:
            return None
        return self._remember(goal, "R2", (axiom_proof, subproofs[0]))

    def _prove(self, goal: Formula, depth: int) -> _Derivation | None:
        if not self._fits(goal):
            return None
        if goal in self.proved:
            return self.proved[goal]
        if goal in self.active or not self._spend_step():
            return None
        self.targets.add(goal)
        self.active.add(goal)
        try:
            axiom_lines = initialize_axioms([goal])
            if axiom_lines:
                line = axiom_lines[0]
                return self._remember(goal, line.rule, substitution=line.substitution)
            if self._is_tautology(goal):
                return self._remember(goal, "R1")
            proof = self._from_known_implications(goal)
            if proof is not None:
                return proof
            for strategy in target_strategies(goal):
                proof = self._try_strategy(goal, strategy, depth)
                if proof is not None:
                    return proof
                if goal in self.proved:
                    return self.proved[goal]
            return self._from_known_implications(goal)
        finally:
            self.active.remove(goal)

    def _extract_proof(self, derivation: _Derivation) -> list[ProofLine]:
        proof_lines: list[ProofLine] = []
        indices: dict[Formula, int] = {}

        def visit(current: _Derivation) -> int:
            if current.formula in indices:
                return indices[current.formula]
            references = tuple(visit(premise) for premise in current.premises)
            index = len(proof_lines)
            proof_lines.append(ProofLine(current.formula, current.rule, references, current.substitution))
            indices[current.formula] = index
            return index

        visit(derivation)
        if not check_proof(derivation.formula, proof_lines):
            raise RuntimeError()
        return proof_lines

    def run(self, goal: Formula) -> SearchResult:
        derivation = self._prove(goal, depth=0)
        return SearchResult(
            proof=self._extract_proof(derivation) if derivation is not None else None,
            reason="proved" if derivation is not None else "no proof found within bounds",
            steps=self.steps,
            targets_seen=len(self.targets),
            r1_checks=self.r1_checks,
            limits_hit=tuple(sorted(self.limits_hit)),
        )


def prove(goal: Formula, *, limits: SearchLimits | None = None) -> SearchResult:
    return _Search(limits or SearchLimits()).run(goal)
