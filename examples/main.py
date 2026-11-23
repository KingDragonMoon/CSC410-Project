from c3_search import SearchResult, prove
from ltl.formula import Always, And, Atom, Eventually, Iff, Implies, Next, Not, Or


def propositional_identity() -> SearchResult:
    """p ⊃ p"""
    proposition = Atom("p")
    return prove(Implies(proposition, proposition))


def next_negation() -> SearchResult:
    """○¬p ≡ ¬○p"""
    proposition = Atom("p")
    return prove(Iff(Next(Not(proposition)), Not(Next(proposition))))


def reversed_next_negation() -> SearchResult:
    """¬○p ≡ ○¬p"""
    proposition = Atom("p")
    return prove(Iff(Not(Next(proposition)), Next(Not(proposition))))


def eventually_conjunction_duality() -> SearchResult:
    """◇(p ∧ q) ≡ ¬□¬(p ∧ q)"""
    conjunction = And(Atom("p"), Atom("q"))
    return prove(Iff(Eventually(conjunction), Not(Always(Not(conjunction)))))


def always_now() -> SearchResult:
    """□p ⊃ p"""
    proposition = Atom("p")
    return prove(Implies(Always(proposition), proposition))


def now_implies_eventually() -> SearchResult:
    """p ⊃ ◇p"""
    proposition = Atom("p")
    return prove(Implies(proposition, Eventually(proposition)))


def temporal_disjunction() -> SearchResult:
    """p ∨ (□q ⊃ q)"""
    first_atom, second_atom = Atom("p"), Atom("q")
    return prove(Or(first_atom, Implies(Always(second_atom), second_atom)))


def temporal_implication() -> SearchResult:
    """p ⊃ (□q ⊃ q)"""
    first_atom, second_atom = Atom("p"), Atom("q")
    return prove(Implies(first_atom, Implies(Always(second_atom), second_atom)))


def temporal_contradiction() -> SearchResult:
    """(□p ∧ ¬p) ⊃ q"""
    first_atom, second_atom = Atom("p"), Atom("q")
    return prove(Implies(And(Always(first_atom), Not(first_atom)), second_atom))


def temporal_equivalence() -> SearchResult:
    """□p ≡ (□p ∧ p)"""
    proposition = Atom("p")
    return prove(Iff(Always(proposition), And(Always(proposition), proposition)))


def next_conjunction_projection() -> SearchResult:
    """○(p ∧ q) ⊃ ○p"""
    first_atom, second_atom = Atom("p"), Atom("q")
    return prove(Implies(Next(And(first_atom, second_atom)), Next(first_atom)))


def nested_temporal_consequences() -> SearchResult:
    """□□((□(p ∧ (q ∧ r)) ⊃ (□p ∧ □q)) ∧ (○(p ∧ (q ∧ r)) ⊃ ○p))"""
    first_atom, second_atom, third_atom = Atom("p"), Atom("q"), Atom("r")
    conjunction = And(first_atom, And(second_atom, third_atom))
    boxed_distribution = Implies(
        Always(conjunction),
        And(Always(first_atom), Always(second_atom)),
    )
    next_projection = Implies(Next(conjunction), Next(first_atom))
    return prove(Always(Always(And(boxed_distribution, next_projection))))


def assignment_eventually_monotonicity() -> SearchResult:
    """□(p ⊃ q) ⊃ (◇p ⊃ ◇q)"""
    first_atom, second_atom = Atom("p"), Atom("q")
    return prove(Implies(
        Always(Implies(first_atom, second_atom)),
        Implies(Eventually(first_atom), Eventually(second_atom)),
    ))


def always_distribution_forward() -> SearchResult:
    """□(p ∧ q) ⊃ (□p ∧ □q)"""
    first_atom, second_atom = Atom("p"), Atom("q")
    return prove(Implies(
        Always(And(first_atom, second_atom)),
        And(Always(first_atom), Always(second_atom)),
    ))


def always_distribution_backward() -> SearchResult:
    """(□p ∧ □q) ⊃ □(p ∧ q)"""
    first_atom, second_atom = Atom("p"), Atom("q")
    return prove(Implies(
        And(Always(first_atom), Always(second_atom)),
        Always(And(first_atom, second_atom)),
    ))


def assignment_always_distributes_over_conjunction() -> SearchResult:
    """□(p ∧ q) ≡ (□p ∧ □q)"""
    first_atom, second_atom = Atom("p"), Atom("q")
    return prove(Iff(
        Always(And(first_atom, second_atom)),
        And(Always(first_atom), Always(second_atom)),
    ))


def main() -> None:
    examples = (
        propositional_identity,
        next_negation,
        reversed_next_negation,
        eventually_conjunction_duality,
        always_now,
        now_implies_eventually,
        temporal_disjunction,
        temporal_implication,
        temporal_contradiction,
        temporal_equivalence,
        next_conjunction_projection,
        nested_temporal_consequences,
        assignment_eventually_monotonicity,
        always_distribution_forward,
        always_distribution_backward,
        assignment_always_distributes_over_conjunction,
    )
    proved_count = 0
    for example in examples:
        print(example.__doc__)
        result = example()
        proved_count += int(result.proved)
        status = "PROVED" if result.proved else "NOT PROVED"
        print(f"{result.steps} steps: {status}\n")
    print(f"Proved {proved_count}/{len(examples)}.")


if __name__ == "__main__":
    main()
