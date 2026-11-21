from ltl.formula import Always, And, Eventually, Formula, Iff, Implies, Next, Not, Or, WeakUntil

AXIOMS = ("A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8")


def instantiate_axiom(name: str, *substitution: Formula) -> Formula:
    arity = 1 if name in ("A1", "A3", "A5", "A6") else 2
    if name not in AXIOMS or len(substitution) != arity:
        raise ValueError("Unknown axiom or incorrect number of substitutions.")
    p = substitution[0]
    q = substitution[1] if arity == 2 else p
    match name:
        case "A1": return Iff(Eventually(p), Not(Always(Not(p))))
        case "A2": return Implies(Always(Implies(p, q)), Implies(Always(p), Always(q)))
        case "A3": return Iff(Next(Not(p)), Not(Next(p)))
        case "A4": return Implies(Next(Implies(p, q)), Implies(Next(p), Next(q)))
        case "A5": return Implies(Always(p), And(p, And(Next(p), Next(Always(p)))))
        case "A6": return Implies(Always(Implies(p, Next(p))), Implies(p, Always(p)))
        case "A7": return Implies(Always(p), WeakUntil(p, q))
        case "A8": return Iff(WeakUntil(p, q), Or(q, And(p, Next(WeakUntil(p, q)))))
