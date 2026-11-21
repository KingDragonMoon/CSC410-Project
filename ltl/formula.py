from dataclasses import dataclass


class Formula:
    pass


@dataclass(frozen=True)
class Atom(Formula):
    name: str


@dataclass(frozen=True)
class Not(Formula):
    body: Formula


@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula


@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula


@dataclass(frozen=True)
class Implies(Formula):
    left: Formula
    right: Formula


@dataclass(frozen=True)
class Iff(Formula):
    left: Formula
    right: Formula


@dataclass(frozen=True)
class Next(Formula):
    body: Formula


@dataclass(frozen=True)
class Always(Formula):
    body: Formula


@dataclass(frozen=True)
class Eventually(Formula):
    body: Formula


@dataclass(frozen=True)
class WeakUntil(Formula):
    left: Formula
    right: Formula