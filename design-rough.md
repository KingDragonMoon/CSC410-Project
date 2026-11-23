The engine searches backward from a goal formula to facts it can prove directly. It then assembles those facts into a forward proof. The aim is to keep the search focused, limit the number of alternatives at each target, and produce reasonably short proofs.

An earlier approach worked bottom up by generating potentially useful axiom instances and combining known facts. This produced too many combinations and many formulas unrelated to the goal. The current approach generates axiom instances and intermediate targets in response to the formula being proved.

The code has three main responsibilities:

- `c3_search` chooses targets and constructs proofs.
- `c2_propositional` uses Z3 to check proposed propositional tautologies. Temporal expressions are treated as indivisible Boolean variables, so this component cannot establish temporal relationships by itself.
- `c1_checker` checks the completed proof against the axioms and inference rules.

Formulas are immutable trees from `ltl/formula.py`. Structural equality lets the engine match patterns, detect repeated targets, and reuse proofs. Search currently uses A1 through A6 and does not support weak until.

Calling `prove(goal)` creates a fresh search. The main flow is:

1. `_prove` checks the formula size and reuses an existing proof if available. It rejects a recursive revisit to a target already being explored.
2. `initialize_axioms` checks whether the whole target matches an axiom. Matching binds schema placeholders to complete formula subtrees. Repeated placeholders must receive the same formula.
3. If no axiom matches, the engine asks whether the target itself is an R1 tautology.
4. For an implication, it also tries deriving the target propositionally from a known implication with the same antecedent.
5. `target_strategies` proposes alternatives. `_try_strategy` recursively proves the prerequisites for each alternative and combines them into a proof of the target. Search follows one alternative at a time and returns the first proof it finds.
6. `_extract_proof` converts the successful derivation into ordered `ProofLine` objects, keeping shared dependencies once. `check_proof` must accept the result before it is returned.

A target is any formula the engine is currently trying to prove. The initial target is the user's goal. A strategy describes a sufficient set of prerequisite targets and how their proofs would establish the current target. All prerequisites within one strategy must succeed. Different strategies are alternatives.

The operator strategies are:

- For `□a`, prove `a`, then apply R3.
- For `a ∧ b`, prove both sides and combine them using R1 and R2.
- For `a ∨ b`, try proving either side.
- For `a ⊃ b`, try proving `¬a` or proving `b`. These are sufficient routes, not all possible proofs of an implication. The engine does not assume `a` locally.
- For `a ⊃ (b ∧ c)`, also try proving `a ⊃ b` and `a ⊃ c`.
- For `a ≡ b`, try the reversed equivalence, then try proving both implications. The active-target check prevents endless reversal.

There are also strategies based on axiom structure. A matching axiom consequent suggests its antecedent as a prerequisite. A conjunct of an axiom consequent can work similarly, with a propositional step extracting that conjunct. For implication goals, matching the antecedent or its conjuncts can identify useful axiom instances. The engine also checks whether either orientation of the corresponding equivalence directly matches an axiom.

This is more than repeatedly splitting the original formula into subformulas. Strategies can introduce new formulas, and not every operator has a direct splitting strategy. In particular, negation, next, and eventually rely on axiom matching or propositional reasoning rather than dedicated recursive decomposition.

For example, to prove `□(p ∧ q) ⊃ □p`, matching the consequent of A2 suggests the target `□((p ∧ q) ⊃ p)`. R3 then suggests `(p ∧ q) ⊃ p`, which is a tautology. The engine builds the proof forward using R1, R3, A2, and R2.

When combining proved prerequisites, `_combine` constructs a formula such as `fact₁ ⊃ (fact₂ ⊃ target)`. If it is a tautology, the engine records it through R1 and applies explicit R2 steps. `_remember` saves proved facts, and `_propagate_r2` immediately derives a consequent whenever both a concrete implication and its antecedent are known. This is a small amount of forward reasoning inside the mainly backward search.

The branching factor depends on the available strategies and structural matches. Strategies are generated lazily, and the engine does not enumerate every substitution from a candidate pool. Depth, formula size, search steps, and proof length are bounded. These choices encourage focused search, but they do not guarantee a small search tree or the shortest proof. A step count measures search work, not proof lines.

The main limitation is discovering useful intermediate formulas. R1 can check a proposed tautology, and the engine can construct tautologies that combine selected facts. It does not freely invent helper formulas or rewrite temporal expressions throughout a goal. As a result, it can miss simple valid formulas such as `p ⊃ ◇p`. Failure means no proof was found by the available strategies within the bounds, not that the goal is invalid.

A practical improvement is to add a small library of useful derived lemmas, such as `p ⊃ ◇p` or `(□p ∧ □q) ⊃ □(p ∧ q)`, and match them like axiom schemas. Each lemma should have a proof using the existing axioms and rules that can be expanded into the final checked proof. This gives search useful shortcuts without changing what the checker trusts. Adding genuinely new axioms instead would require changing the checker and justifying those axioms separately.
