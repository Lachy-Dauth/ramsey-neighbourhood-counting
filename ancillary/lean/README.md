# lean: Lean 4 formalisation of the local lemmas, of R(3,3,6) <= 88 and of the finite checks

**What it proves.** A Lake project of seven Lean 4 files, with no `sorry`, that formalises:

* the local lemmas of Sections 2 and 3 (Lemmas 2.1, 2.3, 2.4, 3.1, 3.2, 3.4, 3.5 and Corollary 2.2), as
  statements about colourings;
* Theorem 4.1, R(3,3,6) <= 88, end to end: from R(3,6) <= 18 and R(3,3,4) <= 30 to R(3,3,6) <= 88, all three in
  the conventional form (every colouring of the edges of K_B has a clique of the required size in some colour);
* the neighbourhood recurrence (1), with its parity refinement, for any number of colours, and Corollary 8.7;
* Lemma 9.2, the certifier lemma of Section 9.1, and the criterion stated after it;
* step (iii), the finite numerical check, of the hand proofs of Theorems 4.1, 4.3, 4.5, 6.2, 6.3, 6.4, 7.4,
  Proposition 6.5 and Lemmas 4.2 and 4.4.

References such as "Lemma 2.1" are to the paper's numbering. The Lean comments cite the paper's LaTeX labels
instead (`lem:caps` is Lemma 2.1, `thm:336` is Theorem 4.1, and so on). The table gives the main theorems.

| paper | Lean (file, namespace `RamseyLean.<File>` unless stated) |
|---|---|
| Lemma 2.1 (local caps) | `Caps.local_caps`, `local_caps_degree`, `local_caps_common`, and `local_caps_degree_R`, `local_caps_common_R` with the constants R(.) - 1; the case t = (3,3,k): `Caps.cap_C12_33k`, `RamseyLocal.mixedNeighbourhood_card_le` |
| Corollary 2.2 | `Caps.handshake_cap`, `handshake_cap_R`; for t = (3,3,k): `RamseyLocal.local_ordered_edge_bound` |
| Lemma 2.3 (caps on several neighbourhoods) | `Caps.multicaps`, `multicaps_R` |
| Lemma 2.4 (corner identities) | `Caps.corner_identities` (`corner_choose`, `corner_mono`, `corner_mixed`, `corner_apex`); the apex count `R336.triangles_eq_sum_edgesInside`, `RamseyLocal.unique_repeated_apex` |
| Lemma 3.1 (apex bound) | `R336.apex_bound` |
| Lemma 3.2 (common-neighbour inequality) | `R336.commonnbr` (without the bracket), `R336.commonnbr_bracket` (with p_k) |
| Lemma 3.4 | `Lemmas.lem_line_a`, `Lemmas.lem_line_b`; the arithmetic alone: `FiniteChecks.line_a`, `line_a_ceil`, `line_b` |
| Lemma 3.5 | `Lemmas.lem_delete_a`, `Lemmas.lem_delete_b` |
| Theorem 4.1, R(3,3,6) <= 88 | `R336.ramseyLE_336_88`, `R336.r336`; step (iii) also as `FiniteChecks.thm336_contradiction` |
| Lemma 4.2, Theorem 4.3, Lemma 4.4, Theorem 4.5 | step (iii): `FiniteChecks.lem_m6more`, `thm337_contradiction`, `lem_m7_124` and `m7_step`, `thm338_contradiction` |
| Theorems 6.2, 6.3, 6.4 | step (iii): `FiniteChecks.thm345_contradiction`, `thm346_contradiction`, `thm355_contradiction` |
| Proposition 6.5 | step (iii): `FiniteChecks.prop_supp_347`, `prop_supp_348`, `prop_supp_356` (and `_unstarred`, `_contradiction`) |
| Theorem 7.4, R(4,4,4) <= 226 | step (iii): `FiniteChecks.thm444a_contradiction` |
| recurrence (1) and its parity refinement | `Recurrence.ramsey_recurrence`, `ramsey_recurrence_parity`, `ramsey_recurrence_paper` |
| Corollary 8.7 | `Recurrence.cor_four`, `cor_four_from_r334` |
| Lemma 9.2 | `Lemmas.lem_cert`, `lem_cert_core`, and the criterion after it, `greenClique_card_le_of_certifiers` |

## The files

A colouring is a function `c : V → V → colour` on a finite vertex set, assumed symmetric (`c x y = c y x`).
`Caps.lean`, `Recurrence.lean` and `Lemmas.lean` never read its diagonal. `LocalCombinatorics.lean` and, internally,
`R336.lean` take the diagonal green; `ConventionalDefinitions.lean` shows that this loses nothing, and `R336.r336`
removes the assumption.

**`LocalCombinatorics.lean`** (namespace `RamseyLocal`). The colours `red`, `blue`, `green`, and the hypotheses
`NoMonoTriangle c a` and `AvoidsGreenK c k` (every green clique has fewer than k vertices).

* `mixedNeighbourhood_card_le`: with no red or blue triangle and no green K_k, for any vertices v and u, the
  vertices w with `c v w` red and `c u w` blue form a green clique, so there are at most k-1 of them. This is
  the cap C_12 = k-1 of Lemma 2.1 for t = (3,3,k).
* `local_ordered_edge_bound` (and `_swap`, red and blue interchanged): the sum over u in N_1(v) of
  |N_1(v) ∩ N_2(u)| is at most (k-1) d_1(v). Its left side is 2 e_2(N_1(v)), so this is
  2 e_2(N_1(v)) <= (k-1) d_1(v), Corollary 2.2 for t = (3,3,k). It is the local step of Lemma 3.1.
* `unique_repeated_apex`: in a colouring with no red or blue triangle, each triangle of H (all three edges red or
  blue) has exactly one apex, and every other triangle has none. This is the pointwise identity behind
  T(H) = Σ_v (e_2(N_1(v)) + e_1(N_2(v))) (Lemma 2.4 with M_1 = M_2 = 0).

**`ConventionalDefinitions.lean`** (namespace `RamseyLocal`). `noMonoTriangle_of_distinct` and
`avoidsGreenK_iff_no_exact`: the conventions of `LocalCombinatorics.lean` (ordered triangles, cliques of size at
least k) agree with the usual ones (three distinct vertices, cliques of size exactly k).

**`Caps.lean`** (namespace `RamseyLean.Caps`). Section 2, for any type of colours. A vector t is a function from
the colours to ℕ, and `Avoids c t` says that for no colour l is there a colour-l clique on t_l vertices.

* Lemma 2.1. `local_caps_degree`: if c is t-avoiding, then d_i(v) <= D for every D such that every vertex set on
  which c is (t - e_i)-avoiding has at most D vertices. `local_caps_common`: for u in N_i(v),
  |N_i(v) ∩ N_j(u)| <= C for every C such that every vertex set on which c is (t - e_i - e_j)-avoiding has at most
  C vertices. `local_caps` is both together. `local_caps_degree_R` and `local_caps_common_R` state the caps with
  the paper's constants R(t - e_i) - 1 and R(t - e_i - e_j) - 1, where `ramseyNumber` is the least n with
  R(.) <= n, given that one exists.
* Corollary 2.2. `handshake_cap`: e_j(N_i(v)) <= ⌊C d_i(v)/2⌋, with C as in `local_caps_common`
  (`handshake_cap_R` with C = R(t - e_i - e_j) - 1).
* Lemma 2.3. `multicaps`: for a set Y of vertices and a map a from Y to the colours, let w_l be the largest order of
  a colour-l clique in {y in Y : a(y) = l}. Then |⋂_{y in Y} N_{a(y)}(y)| <= B for every B that caps the vertex
  sets on which c is (t - w)-avoiding (`multicaps_R` with B = R(t - w) - 1). The statement does not need Y
  nonempty. `multicaps_singleton`, `multicaps_pair`, `local_caps_degree_via_multicaps` and
  `local_caps_common_via_multicaps` are the remark that Lemma 2.1 is the case |Y| <= 2.
* Lemma 2.4. `corner_identities`: in every 3-colouring of K_n, for every colour i,
  Σ_v binom(d_i(v), 2) = 3M_i + Σ_{l ≠ i} T_{i,l} and 3M_i = Σ_v e_i(N_i(v)), and for every j ≠ i,
  Σ_v d_i(v) d_j(v) = 2T_{i,j} + 2T_{j,i} + X and T_{i,j} = Σ_v e_j(N_i(v)). The four identities are also
  `corner_choose`, `corner_mono`, `corner_mixed`, `corner_apex`; all but `corner_mixed` hold for any number of
  colours.
* The examples after Lemma 2.1 for t = (3,3,k), with every hypothesis discharged: `cap_C12_33k`, `cap_C21_33k`
  (C_12 = C_21 = k-1) and `cap_C11_33k`, `cap_C22_33k` (C_11 = C_22 = 0). `avoids_33k_iff` relates `Avoids` to
  the hypotheses of `LocalCombinatorics.lean`.

**`R336.lean`** (namespace `RamseyLean.R336`). Section 3 for t = (3,3,k), and Theorem 4.1.
`AvoidsOn c s₁ s₂ s₃ S` says that S contains no red K_{s₁}, no blue K_{s₂} and no green K_{s₃}.
`RamseyLE s₁ s₂ s₃ B` is the conventional R(s₁,s₂,s₃) <= B (every symmetric 3-colouring on `Fin B` has a red
K_{s₁}, a blue K_{s₂} or a green K_{s₃}), and `RamseyLE2 s t B` the conventional two-colour R(s,t) <= B. H is
`mergedGraph c`, the Mathlib `SimpleGraph` of the red and blue edges, and h_v is its degree; T(H) is the number of
its 3-cliques.

* `red_degree_le`, `blue_degree_le`, `avoidsOn_common_green`: the parts of Lemma 2.1 used here.
  `degree_admissible`: every h_v is admissible, n-1-D_3 <= h_v <= min(n-1, 2D).
* `triangles_eq_sum_edgesInside`: T(H) = Σ_v (e_2(N_1(v)) + e_1(N_2(v))) when there is no red or blue triangle.
* Lemma 3.1. `apex_bound`: in a (3,3,k)-avoiding colouring whose red and blue degrees are capped by D (given as caps
  on the (2,3,k)- and (3,2,k)-avoiding vertex sets), T(H) <= Σ_v A_k(h_v) and 2 Σ_v A_k(h_v) <= (k-1) Σ_v h_v,
  with A_k as in the paper (`apexA`). `apex_bound_k6` is the case k = 6, D = 17.
* Lemma 3.2. `commonnbr`: for k >= 2 and U such that every (3,3,k-2)-avoiding vertex set has fewer than U vertices
  (that is, U >= R(3,3,k-2)), every (3,3,k)-avoiding colouring has Σ_v F_{n,k,U}(h_v) <= 0.
  `commonnbr_bracket`: the same with F + p_k.
* Lemma 3.4(b). `line_b`, in the abstract form used below.
* Theorem 4.1. `r336`: there is no symmetric colouring of an 88-element vertex set with no red K_3, no blue K_3 and
  no green K_6, given three caps: every vertex set with no red edge, no blue triangle and no green K_6 has at most
  17 vertices, the same with red and blue interchanged, and every vertex set with no red or blue triangle and no
  green K_4 has at most 29 vertices. `ramseyLE_336_88`: `RamseyLE2 3 6 18` and `RamseyLE 3 3 4 30` imply
  `RamseyLE 3 3 6 88`, that is, R(3,6) <= 18 and R(3,3,4) <= 30 imply R(3,3,6) <= 88. The proof follows the
  paper: Lemma 2.1 gives h_v <= 34, Lemma 3.2 with n = 88, k = 6, U = 30 gives Σ_v F(h_v) <= 0 with
  F(h) = 3h² - 247h + 4959 = 29 + 43x + 3x² for x = 34 - h, and Lemma 3.4(b) gives the contradiction.

**`Recurrence.lean`** (namespace `RamseyLean.Recurrence`). The recurrence (1), for any finite type of colours.
`RamseyBound t B` says that every symmetric colouring of a complete graph with no colour-i clique on t_i vertices,
for every i, has fewer than B vertices. `ramseyBound_iff_fin` proves this equivalent to the conventional R(t) <= B
on `Fin B`.

* `recurrence_count`: if every colour-i neighbourhood has at most D_i vertices, then n <= Σ_i D_i + 1.
  `parity_obstruction`, `recurrence_parity_count`: the order n = Σ_i D_i + 1 is impossible when Σ_i D_i is even
  and some D_i is odd (by the handshake lemma, `handshake`).
* `ramsey_recurrence`: if R(t - e_i) <= B_i for every colour i, then R(t) <= Σ_i (B_i - 1) + 2.
  `ramsey_recurrence_paper`: with r >= 2 colours and every B_i >= 1, R(t) <= Σ_i B_i - (r - 2), and
  R(t) <= Σ_i B_i - (r - 2) - 1 when Σ_i B_i - (r - 2) is even and some B_i is even. For r = 3 this is (1) and its
  parity refinement (Section 1); for r = 4 it is the recurrence of Section 8.3.
* `RamseyBound.perm` (R is symmetric in its entries) and `RamseyBound.cons_two` (R(2,t) <= R(t)).
* Corollary 8.7. `cor_four`: R(3,4,4) <= 73, R(4,4,4) <= 198 and R(3,3,3,4) <= 149, as hypotheses, imply
  R(3,3,4,4) <= 442, R(3,4,4,4) <= 1521 and R(4,4,4,4) <= 6082. `cor_four_from_r334` replaces R(3,3,3,4) <= 149
  by its inputs R(3,3,4) <= 30 and R(3,3,3,3) <= 62 (`r3334_le`, the recurrence with parity).
* Checks: `r33_le_six` (R(3,3) <= 6) and `r333_le_17` (R(3,3,3) <= 17), with no hypotheses, and `r336_le`, the
  example of Section 1: R(3,6) <= 18 and R(3,3,5) <= 57 imply R(3,3,6) <= 91.

**`FiniteChecks.lean`** (namespace `RamseyLean.FiniteChecks`). Step (iii) of the hand proofs. Nothing here reasons
about colourings: the inequality Σ_v f(profile(v)) <= 0 of step (ii) (from Lemma 3.2, 3.3, 6.1 or 7.3) and the
degree caps that make every profile admissible are explicit hypotheses of the `*_contradiction` theorems. The
checks are polynomial identities (`ring`), the hand positivity arguments (`nlinarith`, `linarith`), and exhaustive
checks over explicit ranges by `decide +kernel` (evaluated by the kernel, so no compiled code is trusted),
`interval_cases` or `norm_num`.

* Section 3: `Admissible`, `Ak` (A_k), `pk` (p_k) with `pk_nonneg` and `pk_values`; `admissible_of_caps`; the
  collecting steps of the proofs of Lemma 3.2 (`commonnbr_collect`) and Lemma 3.3 (`density_collect`).
* Theorem 4.1: `thm336_F_eq`, `thm336_F_shift`, `thm336_F_pos`, `thm336_contradiction`; `thm336_stop` (why the
  argument stops at 88).
* Lemma 4.2: `lem_m6more` (m_6(z) for 79 <= z <= 87 from Σ_v F_{z,6,30}(h_v) <= 0), with display (4)
  (`chord_identity`, `chord_le`) and the rows of its table (`m6_table_beta_alpha`, `m6_q_floor_root`,
  `m6_root_rounding`, `m6_disc`, `m6_ceil`).
* Theorem 4.3: `thm337_admissible`, `thm337_Psi_pos`, `thm337_contradiction`, `thm337_contradiction_caps`;
  `thm337_comparison`.
* Lemma 4.4: `lem_m7_124` (e(H) >= 2495 at order 124) and `m7_step` (m_7(z) = m_7(z-1) + max(0, z-88) for
  125 <= z <= 128, the step of Lemma 3.5(a)).
* Theorem 4.5: `thm338_admissible`, `thm338_Psi_pos`, `thm338_contradiction`, `thm338_contradiction_caps`.
* Section 6: the function Phi of the paper for six weights and the caps C_ij, with and without the floors
  (`PhiFl`, `PhiFF`), and `PhiFF_le_PhiFl` (dropping the floors only lowers Phi, under the sign conditions).
  Theorem 6.2: `thm345_contradiction`, with `w345_coeffs`, `thm345_identity`, `thm345_Phi_ge`, `thm345_choice`,
  `thm345_endpoint`, `thm345_mod3`. Display (5): `wL_forced`, `wL_coeffs`, `L_expansion`. Theorem 6.3:
  `thm346_contradiction`, `thm346_stop`. Theorem 6.4: `thm355_contradiction`, `thm355_stop`.
* Proposition 6.5: `prop_supp_347`, `prop_supp_348`, `prop_supp_356` (the number of admissible profiles and the
  margin, checked over the whole box of profiles), the same without the starred inputs (`_unstarred`, n = 458,
  705, 685), the hand reductions (`supp347_hand`, ...), and the contradiction forms.
* Theorem 7.4: `thm444a_star226` (display (6) from the identities (I), (II), (III) and the five caps at n' = 223),
  `thm444a_profiles`, `thm444a_Phi_pos`, `thm444a_average`, `thm444a_contradiction`; `thm444a_stop_*` (n = 225).
  The star densities of Lemma 7.1, the caps of Lemma 7.2 and the identities of Lemma 7.3 are hypotheses.

**`Lemmas.lean`** (namespace `RamseyLean.Lemmas`). Lemmas 3.4, 3.5 and 9.2.

* Lemma 9.2. `lem_cert_core`: if every green clique of H has at most q vertices and W is a green clique of
  certifiers of A (w and all its red and blue neighbours lie in A), then every green clique T of H - A has
  |T| + |W| <= q. `lem_cert`: the same in the setting of Section 9.1, with F a colouring on the old and the new
  vertices, H its restriction to the old ones and A = A_S. `greenClique_decomp`: every green clique of F is S ∪ T,
  with S a green clique of new vertices and T a green clique of H - A_S. `greenClique_card_le_of_certifiers`: if
  every green clique S of new vertices has a green clique W of certifiers of A_S with |S| <= 1 + |W|, then every
  green clique of F has at most q + 1 vertices.
* Lemma 3.5. `ValidLowerBound k n m` says that e(H) >= m in every (3,3,k;n)-colouring. `lem_delete_a`: if m(n') is
  valid for every n' < n, n >= 1 and R(3,3,k-1) <= B, then m(n-1) + max(0, n-B) is valid for n. `lem_delete_b`:
  ⌈m(s) n(n-1)/(s(s-1))⌉ is valid for n, for 2 <= s < n.
* Lemma 3.4. `lem_line_a`: if every (3,3,k;n)-colouring has Σ_v f(h_v) <= 0, β > 0 and f(h) >= α - βh at every
  admissible h, then every (3,3,k;n)-colouring has e(H) >= nα/(2β), and ⌈nα/(2β)⌉ is valid. `lem_line_b`: if
  n >= 1 and f > 0 at every admissible h, there is no (3,3,k;n)-colouring. Admissibility is defined from
  R(3,k) <= D + 1 and R(3,3,k-1) <= D_3 + 1 (`hdeg_admissible`).

## Inputs assumed

None beyond Mathlib, as axioms. Ramsey numbers enter only as explicit hypotheses, in one of three forms.

* Caps "every vertex set on which c is s-avoiding has at most B vertices" (`Caps`, `R336`, and `Bound33`,
  `BoundRB` in `Lemmas`), which is what the paper uses (|S| <= R(s) - 1).
* `RamseyBound t B` (`Recurrence`).
* The conventional statement on `Fin B`: `RamseyLE`, `RamseyLE2` (`R336`), `RamseyLE` (`Caps`, `Lemmas`).

Bridge lemmas derive the first two forms from the third: `Caps.cap_of_ramseyLE`, `Caps.cap_of_ramseyNumber`,
`R336.card_lt_of_ramseyLE` (with `R336.ramseyLE_swap` and `R336.ramseyLE_of_ramseyLE2`, so that the two-colour
R(3,6) <= 18 serves as R(2,3,6) <= 18 and R(3,2,6) <= 18), `Lemmas.bound33_of_ramseyLE`,
`Lemmas.boundRB_of_ramseyLE` and `Recurrence.ramseyBound_iff_fin`. For instance Theorem 4.1 takes R(3,6) <= 18 and
R(3,3,4) <= 30 as hypotheses, and Corollary 8.7 takes R(3,4,4) <= 73, R(4,4,4) <= 198 and R(3,3,3,4) <= 149. In
`FiniteChecks.lean` the Ramsey inputs enter only as the numeric caps and parameters (D, D_3, U, C_ij, m_k) of each
proof, named in the comments where they are used. No input is proved from scratch, except R(3,3) <= 6 and
R(3,3,3) <= 17, which are proved with no hypotheses as checks of the definitions.

## What is not formalised

* The computer-assisted results and the lemmas behind them: the ladder of Section 5 (Theorem 5.2), the
  five-vertex certificates of Section 8 (Lemma 8.1, Theorems 8.2 to 8.5), the four-vertex certificates with
  several squares of Section 7, and the witnesses of Section 9 (Theorems 9.1 and 9.3). These are checked by the
  programs in `../`.
* Theorem 7.5.
* Lemma 3.3 (density inequality), Lemma 6.1 (weighted triangle identity) and Lemmas 7.1 to 7.3 as statements about
  colourings. Only their arithmetic is formalised (`density_collect`, the coefficients of the weights), and their
  conclusions are hypotheses in `FiniteChecks.lean`. So for Theorems 4.3, 4.5, 6.2, 6.3, 6.4, 7.4, Proposition 6.5
  and Lemmas 4.2 and 4.4 only step (iii) is formalised. Of the bounds of Sections 4, 6 and 7, Theorem 4.1 is the
  only one formalised end to end; Corollary 8.7 is formalised end to end from its three inputs.
* The Ramsey inputs themselves (Table 3 of the paper, and the starred inputs).

## Versions

Lean `leanprover/lean4:v4.24.0` (`lean-toolchain`) and Mathlib tag `v4.24.0`, commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (`lake-manifest.json`, which also pins Batteries, Aesop, Qq and the
other dependencies).

## How to run

    sh check_lean.sh

This needs [elan](https://github.com/leanprover/elan), which provides `lake` and installs the toolchain of
`lean-toolchain`, and git and curl. The script can be run from any directory. It runs `lake exe cache get`, which
on the first run clones Mathlib and its dependencies and downloads about 7300 prebuilt Mathlib files (a few
minutes, about 6 GB in `.lake/`), so Mathlib is never compiled. It then runs `lake build`, which compiles the seven
files. With Mathlib already in place this took about 4 minutes on a 10-core laptop with other jobs running, of
which `FiniteChecks.lean` took about 3. Finally the script fails if Lean reports a `sorry`, if any `#print axioms`
line lists an axiom other than `propext`, `Classical.choice` and `Quot.sound`, or if a source file contains
`sorry`, `admit`, `native_decide` or an `axiom` declaration. The build prints four linter warnings (unused section
variables) in `LocalCombinatorics.lean`, which are harmless. Not run by `run_all.sh`.

## Axioms

Each file ends with `#print axioms` for its main theorems: 188 declarations in all (LocalCombinatorics 4,
ConventionalDefinitions 2, Caps 30, R336 11, Recurrence 17, FiniteChecks 109, Lemmas 15). Each depends on a subset
of `propext`, `Classical.choice` and `Quot.sound`, the standard axioms of Lean and Mathlib: 164 on all three,
14 on `propext` and `Quot.sound`, 2 on `propext` alone, and 8 on none. No declaration depends on `sorryAx` or on
any other axiom. The main theorems (`R336.ramseyLE_336_88`, `R336.r336`, `R336.apex_bound`, `R336.commonnbr`,
`Caps.local_caps`, `Caps.multicaps`, `Caps.corner_identities`, `Recurrence.ramsey_recurrence_paper`,
`Recurrence.cor_four`, `Lemmas.lem_cert`, `Lemmas.lem_delete_a`, `Lemmas.lem_delete_b`, `Lemmas.lem_line_a`,
`Lemmas.lem_line_b` and every `FiniteChecks.*_contradiction`) all print

    depends on axioms: [propext, Classical.choice, Quot.sound]
