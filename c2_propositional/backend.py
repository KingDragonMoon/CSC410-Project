import z3

from ltl.formula import Always, And, Atom, Eventually, Formula, Iff, Implies, Next, Not, Or, WeakUntil


def check_tautology(formula: Formula) -> bool | None:
    # Dictionary that encodes the formula into Z3.
    # For each temporal operator, assign a unique Boolean variable to represent it.
    atoms = {}

    def encode(f):
        kind = type(f)
        if kind is Not:
            return z3.Not(encode(f.body))
        if kind is And:
            return z3.And(encode(f.left), encode(f.right))
        if kind is Or:
            return z3.Or(encode(f.left), encode(f.right))
        if kind is Implies:
            return z3.Implies(encode(f.left), encode(f.right))
        if kind is Iff:
            return encode(f.left) == encode(f.right)
        if kind in (Atom, Next, Always, Eventually, WeakUntil): 
            # if the formula is an atomic proposition or a temporal operator, assign a unique Boolean variable to it
            if f not in atoms:
                atoms[f] = z3.Bool(f"atom_{len(atoms)}")
            return atoms[f]
        raise TypeError(f"Unsupported formula: {kind.__name__}")

    # delegate work to Z3, which will return unsat if the negation of the formula is unsatisfiable
    solver = z3.Solver()
    solver.add(z3.Not(encode(formula)))
    verdict = solver.check()

    # if Z3 returns unsat, then the formula is a tautology
    # if it returns sat, then the formula is not a tautology
    if verdict == z3.unsat:
        return True
    if verdict == z3.sat:
        return False
    return None
