# lean: two facts used in Lemma 3.1 of paper A

**What it proves.** Lean 4 proofs, with no `sorry`, of the two facts behind the apex bound (A, Lemma 3.1),
described in A, Section 10. Nothing else is formalised.

* `local_ordered_edge_bound` (and `local_ordered_edge_bound_swap`, red and blue interchanged), in
  `LocalCombinatorics.lean`: in a 3-colouring with no red or blue triangle and no green K_k, the sum over
  u in N_1(v) of |N_1(v) ∩ N_2(u)| is at most (k-1) d_1(v). Its left side is 2 e_2(N_1(v)), so this is the bound
  2 e_2(N_1(v)) <= (k-1) d_1(v) of A, Lemma 2.1 and Corollary 2.2. It rests on `mixedNeighbourhood_card_le`, the cap
  |N_1(v) ∩ N_2(u)| <= k-1.
* `unique_repeated_apex`, in `LocalCombinatorics.lean`: the pointwise identity behind A, Lemma 2.4. In a colouring with
  no red or blue triangle, each triangle of H (all three edges red or blue) contributes exactly 1 to the apex
  count, at its unique apex, and every other triangle contributes 0.

`ConventionalDefinitions.lean` shows that the conventions used in `LocalCombinatorics.lean` (ordered triangles,
cliques of size at least k) agree with the usual ones (three distinct vertices, cliques of size exactly k).

**Inputs assumed.** None beyond Mathlib. The files import `Mathlib.Tactic` and a few `Mathlib` modules on
`Finset` cardinalities and big operators. The `#print axioms` lines at the end of `LocalCombinatorics.lean`
list the axioms used.

**How to run.** No `lakefile` or `lean-toolchain` is included, and the Lean and Mathlib versions used were not
recorded. To check the files, put both in the library of a Lake project that depends on Mathlib, as top-level
modules (`ConventionalDefinitions.lean` imports `LocalCombinatorics`), and build it. Not run by `run_all.sh`.
