module C0 {

  // Formulas are abstract syntax trees of LTL expressions. An example formula is:
  //Always(
  //  Implies(
  //      Atom("p"),
  //      Atom("q")
  //  )
  //)
  datatype Formula =
      Atom(name: string)
    | Not(body: Formula)
    | And(left: Formula, right: Formula)
    | Or(left: Formula, right: Formula)
    | Implies(left: Formula, right: Formula)
    | Iff(left: Formula, right: Formula)
    | Next(body: Formula)
    | Always(body: Formula)
    | Eventually(body: Formula)
    | WeakUntil(left: Formula, right: Formula)

  // LTL formulas are formulas evaluated over an infinite sequence of states. 
  // A trace supplies the truth of every atomic proposition at every natural time. (How the propositions behave over time)
  // nat: a natural number representing time 
  // string: the name of an atomic proposition 
  // bool: the truth value of that atomic proposition at that time
  // so something like trace(0, "p") would be true if "p" is true at time 0, and false otherwise
  type Trace = (nat, string) -> bool

  // Define what each formua means in terms of the trace. The meaning of a formula is a function from time to truth value.
  // Meaning will show us how formulas behave over time.
  // Example:Meaning(trace, Atom("p"))(0) would return true if "p" is true at time 0 in the given trace, and false otherwise.
  ghost function Meaning(trace: Trace, formula: Formula): nat -> bool
    decreases formula
  {
    match formula
    case Atom(name) => (time: nat) => trace(time, name)
    case Not(p) =>
      var pv := Meaning(trace, p);
      (time: nat) => !pv(time)
    case And(p, q) =>
      var pv := Meaning(trace, p);
      var qv := Meaning(trace, q);
      (time: nat) => pv(time) && qv(time)
    case Or(p, q) =>
      var pv := Meaning(trace, p);
      var qv := Meaning(trace, q);
      (time: nat) => pv(time) || qv(time)
    case Implies(p, q) =>
      var pv := Meaning(trace, p);
      var qv := Meaning(trace, q);
      (time: nat) => pv(time) ==> qv(time)
    case Iff(p, q) =>
      var pv := Meaning(trace, p);
      var qv := Meaning(trace, q);
      (time: nat) => pv(time) <==> qv(time)
    case Next(p) =>
      var pv := Meaning(trace, p);
      (time: nat) => pv(time + 1)
    case Always(p) =>
      var pv := Meaning(trace, p);
      (time: nat) => forall future: nat :: time <= future ==> pv(future)
    case Eventually(p) =>
      var pv := Meaning(trace, p);
      (time: nat) => exists future: nat :: time <= future && pv(future)
    case WeakUntil(p, q) =>
      var pv := Meaning(trace, p);
      var qv := Meaning(trace, q);
      (time: nat) =>
        (forall future: nat :: time <= future ==> pv(future)) // p holds forever
        || (exists end: nat :: time <= end && qv(end)         // q eventually becomest true
              && (forall before: nat :: time <= before < end ==> pv(before)))
  }

  // Holds is a wrapper for the meaning function, it checks if a formula holds at a specific time in a given trace.
  ghost predicate Holds(trace: Trace, time: nat, formula: Formula)
  {
    Meaning(trace, formula)(time)
  }

  // Validity is truth on every infinite trace, at every time. making it true under every interpretation.
  ghost predicate Valid(formula: Formula)
  {
    forall trace: Trace, time: nat :: Holds(trace, time, formula) // the formula holds for every possible trace and time.
  }

  // Lemmas for unfolding the eventually and always temporal operators, which are used in the soundness proofs.
  lemma UnfoldEventually(trace: Trace, time: nat, p: Formula)
    ensures Holds(trace, time, Eventually(p))
      == (exists future: nat :: time <= future && Holds(trace, future, p))
  {
    var pv := Meaning(trace, p);

    assert Meaning(trace, Eventually(p))
      == ((now: nat) => exists future: nat :: now <= future && pv(future));

    assert Holds(trace, time, Eventually(p))
      == (exists future: nat :: time <= future && pv(future));

    forall future: nat
      ensures Holds(trace, future, p) == pv(future)
    {
    }
  }

  lemma UnfoldAlways(trace: Trace, time: nat, p: Formula)
    ensures Holds(trace, time, Always(p))
      == (forall future: nat :: time <= future ==> Holds(trace, future, p))
  {
    var pv := Meaning(trace, p);

    assert Meaning(trace, Always(p))
      == ((now: nat) => forall future: nat :: now <= future ==> pv(future));

    assert Holds(trace, time, Always(p))
      == (forall future: nat :: time <= future ==> pv(future));

    forall future: nat
      ensures Holds(trace, future, p) == pv(future)
    {
    }
  }

  // R1's mathematical specification
  // Descend through Boolean connectives, but STOP at a temporal constructor.
  // We do not need to unfold temporal operators, because R1 is for propositional tautologies. 
  // We can just check the truth of the formula at a single time point, without considering its behavior over time.
  // Thus treating temporal subformulas as boolean variables is sufficient.

  // A valuation is a function that assigns truth values to formulas. It is used to evaluate the truth of formulas in a propositional context.
  type PropValuation = Formula -> bool

  ghost function PropEval(valuation: PropValuation, formula: Formula): bool
    decreases formula
  {
    match formula
    case Not(p) => !PropEval(valuation, p)
    case And(p, q) => PropEval(valuation, p) && PropEval(valuation, q)
    case Or(p, q) => PropEval(valuation, p) || PropEval(valuation, q)
    case Implies(p, q) => PropEval(valuation, p) ==> PropEval(valuation, q)
    case Iff(p, q) => PropEval(valuation, p) <==> PropEval(valuation, q)
    case Atom(_) => valuation(formula)
    case Next(_) => valuation(formula)
    case Always(_) => valuation(formula)
    case Eventually(_) => valuation(formula)
    case WeakUntil(_, _) => valuation(formula)
  }

// A tautology is a formula that is true under every possible valuation. 
// It is a propositional formula that is always true, regardless of the truth values of its atomic propositions.  
  ghost predicate Tautology(formula: Formula)
  {
    forall valuation: PropValuation :: PropEval(valuation, formula)
  }

  datatype Axiom = A1 | A2 | A3 | A4 | A5 | A6 | A7 | A8

  // p and q are whole formulas, not only atomic propositions
  function Instantiate(axiom: Axiom, p: Formula, q: Formula): Formula
  {
    match axiom
    case A1 => Iff(Eventually(p), Not(Always(Not(p))))
    case A2 => Implies(Always(Implies(p, q)),
                       Implies(Always(p), Always(q)))
    case A3 => Iff(Next(Not(p)), Not(Next(p)))
    case A4 => Implies(Next(Implies(p, q)), Implies(Next(p), Next(q)))
    case A5 => Implies(Always(p), And(p, And(Next(p), Next(Always(p)))))
    case A6 => Implies(Always(Implies(p, Next(p))), Implies(p, Always(p)))
    case A7 => Implies(Always(p), WeakUntil(p, q))
    case A8 => Iff(WeakUntil(p, q), Or(q, And(p, Next(WeakUntil(p, q)))))
  }

  // determines if a formula is an instance of some axiom schema. 
  // It checks if the formula can be obtained by substituting formulas for the placeholders in an axiom schema.
  ghost predicate IsAxiomInstance(formula: Formula)
  {
    exists axiom: Axiom, p: Formula, q: Formula ::
      formula == Instantiate(axiom, p, q)
  }

// a formula is derivable (has a proof) if it satisfies at least one of four conditions.
// We want the smallest set of formulas containing the axioms and tautologies and closed under R2 and R3.
// Using a least fixpoint ensures that only formulas with finite derivations are included, preventing circular justifications.
  least predicate Derivable[nat](formula: Formula)
  {
    IsAxiomInstance(formula)                                                // if it is an instance of an axiom schema
    || Tautology(formula)                                                   // if it is a propositional tautology (R1)
    || (exists premise: Formula ::                                          // if it can be derived from a premise using modus ponens (R2)
          Derivable(Implies(premise, formula)) && Derivable(premise))
    || (formula.Always? && Derivable(formula.body))                         // if it can be derived from its body using the always rule (R3)
  }

  // PropEval assigns temporal subformulas to truth values, and then evaluates the propositional structure of the formula.
  // Holds checks if a formula is true at a specific time in a given trace, with its temporal meaning.
  // So PropositionalAbstraction ensure that propositional evaluation agrees with LTL satisfaction. (or Holds agrees with PropEval)
  lemma PropositionalAbstraction(trace: Trace, time: nat, formula: Formula)
    ensures PropEval(f => Holds(trace, time, f), formula)
            == Holds(trace, time, formula)
    decreases formula
  {
    match formula {
      case Not(p) => PropositionalAbstraction(trace, time, p);
      case And(p, q) =>
        PropositionalAbstraction(trace, time, p);
        PropositionalAbstraction(trace, time, q);
      case Or(p, q) =>
        PropositionalAbstraction(trace, time, p);
        PropositionalAbstraction(trace, time, q);
      case Implies(p, q) =>
        PropositionalAbstraction(trace, time, p);
        PropositionalAbstraction(trace, time, q);
      case Iff(p, q) =>
        PropositionalAbstraction(trace, time, p);
        PropositionalAbstraction(trace, time, q);
      case Atom(_) =>
      case Next(_) =>
      case Always(_) =>
      case Eventually(_) =>
      case WeakUntil(_, _) =>
    } // Don't need to check temporal operators, because they are treated as atomic propositions in propositional evaluation.
  }

  // R1Sound proves that if a formula is a tautology, then it is valid.
  lemma R1Sound(formula: Formula)
    requires Tautology(formula)
    ensures Valid(formula)
  {
    // To prove validity, we need to show that the formula is true in all traces and at all times.
    forall trace: Trace, time: nat
      ensures Holds(trace, time, formula)
    {
      var valuation: PropValuation := f => Holds(trace, time, f);
      assert PropEval(valuation, formula); // Since the formula is a tautology, it is true under any valuation.
      // so far we have tautology -> PropEval is true, 
      // using propositional abstraction, we can conclude that Holds is true for the formula at the given trace and time.
      PropositionalAbstraction(trace, time, formula);
      // Therefore, the formula holds in all traces and at all times, proving its validity.
    }
  }

  // modus ponens, a simple one
  lemma R2Sound(p: Formula, q: Formula)
    requires Valid(Implies(p, q))
    requires Valid(p)
    ensures Valid(q)
  {
    forall trace: Trace, time: nat
      ensures Holds(trace, time, q)
    {
      // Since Implies(p, q) is valid, it holds in all traces and at all times.
      // Since p is valid, it also holds in all traces and at all times.
      assert Holds(trace, time, Implies(p, q));
      assert Holds(trace, time, p);
      // By the definition of Implies, if p holds, then q must also hold.
    }
  }

  lemma R3Sound(p: Formula)
    requires Valid(p)
    ensures Valid(Always(p))
  {
    forall trace: Trace, time: nat
      ensures Holds(trace, time, Always(p))
    {
      UnfoldAlways(trace, time, p); // unfold tells us that Always(p) holds at time if p holds now, and at all future times.
      forall future: nat | time <= future
        ensures Holds(trace, future, p) // this is automatically satisfied by the assumption that p is valid.
      {
      }
    }
  }

  // Basic semantic lemmas
  lemma AlwaysIncludesPresent(trace: Trace, time: nat, p: Formula)
    requires Holds(trace, time, Always(p))
    ensures Holds(trace, time, p)
  {
  }

  lemma AlwaysPersists(trace: Trace, time: nat, p: Formula)
    requires Holds(trace, time, Always(p))
    ensures Holds(trace, time + 1, Always(p))
  {
    forall future: nat | time + 1 <= future
      ensures Holds(trace, future, p)
    {
    }
  }

  lemma WeakUntilWhenAlways(trace: Trace, time: nat, p: Formula, q: Formula)
    requires Holds(trace, time, Always(p))
    ensures Holds(trace, time, WeakUntil(p, q))
  {
  }

  lemma WeakUntilWhenRightHolds(trace: Trace, time: nat, p: Formula, q: Formula)
    requires Holds(trace, time, q)
    ensures Holds(trace, time, WeakUntil(p, q))
  {
    assert time <= time && Holds(trace, time, q)
      && (forall before: nat ::
            time <= before < time ==> Holds(trace, before, p)); // vacously true
  }

  // A1 soundness
  lemma {:fuel Meaning, 5, 6} A1Sound(trace: Trace, time: nat, p: Formula)
    ensures Holds(trace, time, Instantiate(A1, p, p))
  {
    UnfoldEventually(trace, time, p); 
    UnfoldAlways(trace, time, Not(p));

    if Holds(trace, time, Eventually(p)) {                          // case: eventually p is true
      var future: nat :| time <= future && Holds(trace, future, p); // assume p is eventually true, find a witness 'future' where p holds
      assert !Holds(trace, future, Not(p));                         // since p holds at 'future', Not(p) does not hold at 'future'
      assert !Holds(trace, time, Always(Not(p)));                   // since Not(p) does not hold at 'future', Always(Not(p)) does not hold at 'time'
    } else {
      forall future: nat | time <= future                           // case: eventually p is false
        ensures Holds(trace, future, Not(p))                        // Not(p) holds at all future times
      {
      }
      assert Holds(trace, time, Always(Not(p)));                    // so Not(p) always holds
    }                                                               // in both cases both sides of the equivalence agree, proving the soundness of A1
  }

  // A2: specialize both global hypotheses at the same future position.
  lemma A2Sound(trace: Trace, time: nat, p: Formula, q: Formula)
    ensures Holds(trace, time, Instantiate(A2, p, q))
  {
    if Holds(trace, time, Always(Implies(p, q)))
        && Holds(trace, time, Always(p)) {                          // only need to check this case as others are vacuously true
      UnfoldAlways(trace, time, q);
      forall future: nat | time <= future
        ensures Holds(trace, future, q)
      {
        assert Holds(trace, future, Implies(p, q));                 // from Always(Implies(p, q)) in if statement
        assert Holds(trace, future, p);                             // from Always(p) in if statement
      }
      assert Holds(trace, time, Always(q));
    }
  }

  lemma {:fuel Meaning, 3, 4} A3Sound(trace: Trace, time: nat, p: Formula)
    ensures Holds(trace, time, Instantiate(A3, p, p))
  {
    assert Holds(trace, time, Next(Not(p))) == !Holds(trace, time + 1, p); // Unfolding the meaning of Next(Not(p)) shows that it is equivalent to Not(p) holding at time + 1
    assert Holds(trace, time, Not(Next(p))) == !Holds(trace, time + 1, p); // similarly here, so both sides of the equivalence reduce to the same boolean expression
  }

  lemma {:fuel Meaning, 3, 4} A4Sound(trace: Trace, time: nat, p: Formula, q: Formula)
    ensures Holds(trace, time, Instantiate(A4, p, q))
  {
    assert Holds(trace, time, Next(Implies(p, q)))
      == (Holds(trace, time + 1, p) ==> Holds(trace, time + 1, q));        // again, unfold the meaning of next
    assert Holds(trace, time, Next(p)) == Holds(trace, time + 1, p);       
    assert Holds(trace, time, Next(q)) == Holds(trace, time + 1, q);
  }                                                                        // both sides of the implication reduce to the same boolean expression,
                                                                           // making it a tautology, proving the soundness of A4.
  lemma A5Sound(trace: Trace, time: nat, p: Formula)
    ensures Holds(trace, time, Instantiate(A5, p, p))
  {
    if Holds(trace, time, Always(p)) {                                     // only need to check this case as others are vacuously true
      UnfoldAlways(trace, time, p);                                        // we need to show p, Next(p), and Next(Always(p)) all hold at time
      AlwaysIncludesPresent(trace, time, p);                               // this lemma shows p                          
      AlwaysPersists(trace, time, p);                                      // this lemma shows Next(Always(p)) holds at time
      assert Holds(trace, time + 1, p);
      assert Holds(trace, time, Next(p));                                  // follows from previous assertion
      assert Holds(trace, time, Next(Always(p))); 
      assert Holds(trace, time, And(Next(p), Next(Always(p))));
      assert Holds(trace, time, And(p, And(Next(p), Next(Always(p)))));
    }
  }

  // A6's induction: p holds after any finite number of preserved steps.
  lemma {:induction false} PreservedAtOffset(
      trace: Trace, time: nat, p: Formula, offset: nat)
    requires Holds(trace, time, p)
    requires Holds(trace, time, Always(Implies(p, Next(p))))
    ensures Holds(trace, time + offset, p)
    decreases offset
  {
    if offset > 0 {  // base case if offset = 0, then Holds(trace, time + 0, p) is trivially true since Holds(trace, time, p) is given as a requirement
      PreservedAtOffset(trace, time, p, offset - 1);                    // inductive hypothesis: assume Holds(trace, time + (offset - 1), p) holds
      assert time <= time + (offset - 1);
      assert Holds(trace, time + (offset - 1), Implies(p, Next(p)));   // from Always(Implies(p, Next(p))) in the requires clause
      assert Holds(trace, time + (offset - 1), Next(p));               // from inductive hypothesis and the previous assertion
      assert Holds(trace, time + (offset - 1) + 1, p);                 // from previous assertion, and this is what we wanted to prove: Holds(trace, time + offset, p)
      assert time + (offset - 1) + 1 == time + offset;
    }
  }

  lemma A6Sound(trace: Trace, time: nat, p: Formula)
    ensures Holds(trace, time, Instantiate(A6, p, p))
  {
    if Holds(trace, time, Always(Implies(p, Next(p))))
        && Holds(trace, time, p) {
      UnfoldAlways(trace, time, p);
      forall future: nat | time <= future                               // for every future time, we need to show that p holds at that time
        ensures Holds(trace, future, p)
      {
        PreservedAtOffset(trace, time, p, future - time);               // by inducting on the offset (future - time), we can show that p holds at every future time
        assert time + (future - time) == future;
      }
      assert Holds(trace, time, Always(p));
    }
  }

  // remember that this is in regards to weak-until
  lemma A7Sound(trace: Trace, time: nat, p: Formula, q: Formula)
    ensures Holds(trace, time, Instantiate(A7, p, q))
  {
    if Holds(trace, time, Always(p)) {
      WeakUntilWhenAlways(trace, time, p, q);
    }
  }


  lemma UnfoldWeakUntil(trace: Trace, time: nat, p: Formula, q: Formula)
    ensures Holds(trace, time, WeakUntil(p, q)) ==                                  // Unfolding the meaning of WeakUntil(p, q) shows that
      ((forall future: nat :: time <= future ==> Holds(trace, future, p))           // it is equivalent to either p holding forever or q eventually holding with p holding until then
       || (exists end: nat :: time <= end && Holds(trace, end, q)
             && (forall before: nat ::
                   time <= before < end ==> Holds(trace, before, p))))
  {
    var pv := Meaning(trace, p);
    var qv := Meaning(trace, q);
    assert Meaning(trace, WeakUntil(p, q)) == ((now: nat) =>
      (forall future: nat :: now <= future ==> pv(future))
      || (exists end: nat :: now <= end && qv(end)
            && (forall before: nat :: now <= before < end ==> pv(before))));
    assert Holds(trace, time, WeakUntil(p, q)) ==
      ((forall future: nat :: time <= future ==> pv(future))
       || (exists end: nat :: time <= end && qv(end)
             && (forall before: nat :: time <= before < end ==> pv(before))));
    forall future: nat
      ensures Holds(trace, future, p) == pv(future)
      ensures Holds(trace, future, q) == qv(future)
    {
    }
  }

// for A8, show the forward implication holds
  lemma WeakUntilForward(trace: Trace, time: nat, p: Formula, q: Formula)
    requires Holds(trace, time, WeakUntil(p, q))
    ensures Holds(trace, time, q)
         || (Holds(trace, time, p) && Holds(trace, time + 1, WeakUntil(p, q)))
  {
    if !Holds(trace, time, q) {                      // only need to check this case as if q holds, then the implication is trivially true
      UnfoldWeakUntil(trace, time, p, q);
      UnfoldAlways(trace, time, p);
      if (forall future: nat :: time <= future ==> Holds(trace, future, p)) {          // case A: p holds forever
        assert Holds(trace, time, Always(p));
        AlwaysIncludesPresent(trace, time, p);                                         // then p holds now
        AlwaysPersists(trace, time, p);                                                // then always p holds at time + 1
        WeakUntilWhenAlways(trace, time + 1, p, q);                                    // with previous two assertions, we can conclude that WeakUntil(p, q) holds at time + 1
      } else {
        var end: nat :| time <= end && Holds(trace, end, q)
          && (forall before: nat :: time <= before < end ==> Holds(trace, before, p));  // case B: p holds until q eventually holds
        assert time < end;                                                              // there exists a time in the future where q holds, and p holds until then
        assert Holds(trace, time, p);                                                   // since p holds until q holds, p must hold at the current time
        assert time + 1 <= end && Holds(trace, end, q)                                  // q holds at end, and p holds at all times before end, so we can conclude that WeakUntil(p, q) holds at time + 1
          && (forall before: nat ::
                time + 1 <= before < end ==> Holds(trace, before, p));
        assert Holds(trace, time + 1, WeakUntil(p, q));
      }
    }
  }

// for A8, show the backward implication holds
  lemma WeakUntilBackward(trace: Trace, time: nat, p: Formula, q: Formula)
    requires Holds(trace, time, q)
          || (Holds(trace, time, p) && Holds(trace, time + 1, WeakUntil(p, q)))
    ensures Holds(trace, time, WeakUntil(p, q))
  {
    if Holds(trace, time, q) {                                         // case A: q holds now
      WeakUntilWhenRightHolds(trace, time, p, q);                      // then WeakUntil(p, q) holds now
    } else if (forall future: nat ::                                   // case B: p holds now and WeakUntil(p, q) holds at time + 1 (from precondition)
                 time + 1 <= future ==> Holds(trace, future, p)) {     // additionally assume that p holds forever from time + 1 onwards
      forall future: nat | time <= future                              
        ensures Holds(trace, future, p)
      {
        if future != time {                         // if future = time, then we already know that Holds(trace, time, p) holds from the precondition
          assert time + 1 <= future;                // otherwise, since p holds forever from time + 1 onwards, it must also hold at future
        }
      }
      UnfoldAlways(trace, time, p);
      assert Holds(trace, time, Always(p));
      WeakUntilWhenAlways(trace, time, p, q);       // then since p holds forever, WeakUntil(p, q) holds now
    } else {                                                         // Case C: q eventually occurs
      assert Holds(trace, time + 1, WeakUntil(p, q));                // from the precondition, we know that WeakUntil(p, q) holds at time + 1   
      UnfoldWeakUntil(trace, time + 1, p, q);                        // but since the previous branch is false, we know that p does not hold forever from time + 1 onwards, so we know that q must eventually occur in the future
      var end: nat :| time + 1 <= end && Holds(trace, end, q)
        && (forall before: nat ::
              time + 1 <= before < end ==> Holds(trace, before, p));
      forall before: nat | time <= before < end
        ensures Holds(trace, before, p)
      {
        if before != time {                         // if before = time, then we already know that Holds(trace, time, p) holds from the precondition
          assert time + 1 <= before;                // otherwise, since p holds until q eventually occurs, it must also hold at before
        }
      }
      assert time <= end && Holds(trace, end, q)    // since end >= time + 1, and q holds at end, we can conclude that q holds at some time in the future
        && (forall before: nat :: time <= before < end ==> Holds(trace, before, p));
      assert Holds(trace, time, WeakUntil(p, q)); // therefore, WeakUntil(p, q) holds at time
    }
  }

  // A8: the two directions of the weak-until unfolding equivalence.
  lemma A8Sound(trace: Trace, time: nat, p: Formula, q: Formula)
    ensures Holds(trace, time, Instantiate(A8, p, q))
  {
    if Holds(trace, time, WeakUntil(p, q)) {
      WeakUntilForward(trace, time, p, q);
    }
    if Holds(trace, time, q)
       || (Holds(trace, time, p) && Holds(trace, time + 1, WeakUntil(p, q))) {
      WeakUntilBackward(trace, time, p, q);
    }
    assert Holds(trace, time, Next(WeakUntil(p, q)))                                // showing dafny that the next of 'weak until' is equivalent to 'weak until' at the next time step
      == Holds(trace, time + 1, WeakUntil(p, q));
    assert Holds(trace, time, And(p, Next(WeakUntil(p, q))))
      == (Holds(trace, time, p) && Holds(trace, time + 1, WeakUntil(p, q)));
    assert Holds(trace, time, Or(q, And(p, Next(WeakUntil(p, q)))))
      == (Holds(trace, time, q)
          || (Holds(trace, time, p) && Holds(trace, time + 1, WeakUntil(p, q))));
  }

  lemma AxiomSound(axiom: Axiom, p: Formula, q: Formula)
    ensures Valid(Instantiate(axiom, p, q))             // for every axiom and every formula p and q, the instance of the axiom is valid
  {
    forall trace: Trace, time: nat
      ensures Holds(trace, time, Instantiate(axiom, p, q))
    {
      match axiom {
        case A1 => A1Sound(trace, time, p);
        case A2 => A2Sound(trace, time, p, q);
        case A3 => A3Sound(trace, time, p);
        case A4 => A4Sound(trace, time, p, q);
        case A5 => A5Sound(trace, time, p);
        case A6 => A6Sound(trace, time, p);
        case A7 => A7Sound(trace, time, p, q);
        case A8 => A8Sound(trace, time, p, q);
      }
    }
  }

  // Axiom instance soundness: if a formula is an instance of an axiom, then it is valid.
  lemma AxiomInstanceSound(formula: Formula)
    requires IsAxiomInstance(formula)
    ensures Valid(formula)
  {
    var axiom: Axiom, p: Formula, q: Formula :|
      formula == Instantiate(axiom, p, q);
    AxiomSound(axiom, p, q);
  }

// we have shown that each axiom is valid, and that the inference rules preserve validity.
// Now we can prove that any formula that is derivable using a finite combination of these rules is valid
  lemma {:induction false} SoundnessPrefix(depth: nat, formula: Formula)
    requires Derivable#[depth](formula)        // requires that the formula is derivable within a proof of height 'depth'
    ensures Valid(formula)                     // where each depth is a 'layer of inference' or one application of a rule/axiom
    decreases depth                            // induct on this 'depth'
  {
    assert depth > 0;
    if IsAxiomInstance(formula) {                           // case A: formula is an axiom
      AxiomInstanceSound(formula);                          // then it is valid, as we've already proved it
    } else if Tautology(formula) {                          // case B: formula is a tautology
      R1Sound(formula);                                     // then it is valid, as we've already proved it
    } else if exists premise: Formula ::                    // case C: formula is derived from a premise using modus ponens (R2)
        Derivable#[depth - 1](Implies(premise, formula))
        && Derivable#[depth - 1](premise) {
      var premise: Formula :|                                 
        Derivable#[depth - 1](Implies(premise, formula))
        && Derivable#[depth - 1](premise);
      SoundnessPrefix(depth - 1, Implies(premise, formula));    // recurse on the premise and the implication, which are both derivable at a smaller depth
      SoundnessPrefix(depth - 1, premise);                      // by the inductive hypothesis, both are valid
      R2Sound(premise, formula);                                // then by modus ponens, the formula is valid
    } else {
      assert formula.Always?;                                   // case D: formula is derived from its body using the always rule (R3)
      assert Derivable#[depth - 1](formula.body);               // establish that the body of the formula is derivable at a smaller depth
      SoundnessPrefix(depth - 1, formula.body);                 // recurse on the body, by the inductive hypothesis, it is valid
      R3Sound(formula.body);                                    // then by the always rule, the formula is valid
    }
  }

  // The main theorem : syntactic provability implies LTL validity.
  lemma Soundness(formula: Formula)
    requires Derivable(formula)
    ensures Valid(formula)
  {
    var depth: nat :| Derivable#[depth](formula);
    SoundnessPrefix(depth, formula);
  }
}
