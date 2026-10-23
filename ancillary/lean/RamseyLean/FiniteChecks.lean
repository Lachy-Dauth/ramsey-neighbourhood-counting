import Mathlib.Tactic

/-!
# Finite numerical checks (step (iii)) of the hand proofs

This file formalises the finite numerical checks, step (iii) of the method, in the hand proofs
of `paper/neighbourhood_counting.tex`:

* Theorem `thm:336`, Lemma `lem:m6more`, Theorem `thm:337`, Lemma `lem:m7`, Theorem `thm:338`
  (Section `sec:three`, functions `F` and `Psi` of Lemmas `lem:commonnbr` and `lem:density`);
* Theorems `thm:345`, `thm:346`, `thm:355` and Proposition `prop:supp`
  (Section `sec:types`, the functions `Phi` of the weighted triangle identities);
* Theorem `thm:444a` (Section `sec:444`, the function `Phi` of the four-vertex identity, and the
  linear algebra of its Steps 1 to 3).

Every check is a kernel-checked statement about an explicit integer or rational function on an
explicit range: `ring` for polynomial identities, `nlinarith`/`linarith` for the hand
positivity arguments, and `decide +kernel` (evaluation by the kernel itself, so no compiled code is trusted) or
`interval_cases`/`norm_num` for exhaustive finite checks.

Nothing here reasons about colourings. Step (ii) of each proof, an inequality
`∑_v f(profile v) ≤ 0` (for instance from Lemma `lem:commonnbr`, `lem:density` or
`lem:weighted`), is taken as an explicit hypothesis of the `*_contradiction` theorems, as are
the degree caps that make every profile admissible. The Ramsey inputs enter only as these
numeric caps (and as the numeric parameters `U`, the mixed caps `C_ij`, and the lower bounds
`m_k` built from them), each named where it is used.
-/

namespace RamseyLean
namespace FiniteChecks

open Finset

/-! ## Lemma `lem:line`: the two ways of using `∑_v f(h_v) ≤ 0` -/

/-- Lemma `lem:line`(a), before rounding: if `f h ≥ α - β h` at every admissible `h`, every
`h_v` is admissible and `∑_v f(h_v) ≤ 0`, then `n α ≤ 2 β e(H)`, where `2 e(H) = ∑_v h_v`. -/
theorem line_a {V : Type*} [Fintype V] (f : ℤ → ℤ) (adm : ℤ → Prop) (α β : ℤ)
    (hf : ∀ x, adm x → α - β * x ≤ f x) (h : V → ℤ) (hadm : ∀ v, adm (h v))
    (hsum : ∑ v, f (h v) ≤ 0) (E : ℤ) (hE : 2 * E = ∑ v, h v) :
    (Fintype.card V : ℤ) * α ≤ 2 * β * E := by
  have h1 : ∑ v, (α - β * h v) ≤ ∑ v, f (h v) :=
    Finset.sum_le_sum fun v _ => hf (h v) (hadm v)
  have h2 : ∑ v, (α - β * h v) = (Fintype.card V : ℤ) * α - β * ∑ v, h v := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum, Finset.card_univ,
      nsmul_eq_mul]
  have h3 : β * ∑ v, h v = 2 * β * E := by rw [← hE]; ring
  linarith

/-- Lemma `lem:line`(a), with the rounding: the integer `E` is at least any `m` with
`2β(m-1) < nα`, that is, at least `⌈nα/(2β)⌉`. -/
theorem line_a_ceil {V : Type*} [Fintype V] (f : ℤ → ℤ) (adm : ℤ → Prop) (α β m : ℤ)
    (hβ : 0 < β) (hf : ∀ x, adm x → α - β * x ≤ f x) (h : V → ℤ) (hadm : ∀ v, adm (h v))
    (hsum : ∑ v, f (h v) ≤ 0) (E : ℤ) (hE : 2 * E = ∑ v, h v)
    (hm : 2 * β * (m - 1) < (Fintype.card V : ℤ) * α) : m ≤ E := by
  have := line_a f adm α β hf h hadm hsum E hE
  by_contra hlt
  push_neg at hlt
  have : 2 * β * E ≤ 2 * β * (m - 1) := by
    apply mul_le_mul_of_nonneg_left (by omega) (by omega)
  linarith

/-- Lemma `lem:line`(b): if `n ≥ 1` and `f > 0` at every admissible `h`, then
`∑_v f(h_v) > 0` whenever every `h_v` is admissible. -/
theorem line_b {V : Type*} [Fintype V] [Nonempty V] (f : ℤ → ℤ) (adm : ℤ → Prop)
    (hf : ∀ x, adm x → 0 < f x) (h : V → ℤ) (hadm : ∀ v, adm (h v)) :
    0 < ∑ v, f (h v) :=
  Finset.sum_pos (fun v _ => hf (h v) (hadm v)) Finset.univ_nonempty

/-! ## Section `sec:merge`: the functions `F`, `Psi` and the bracket `p_k` -/

/-- Admissible `H`-degrees (Section `sec:merge`):
`max(0, n-1-D₃) ≤ h ≤ min(n-1, 2D)`, where `D = R(3,k)-1` caps the red and the blue degree
and `D₃ ≥ R(3,3,k-1)-1` caps the green degree. -/
def Admissible (n D D3 h : ℤ) : Prop := max 0 (n - 1 - D3) ≤ h ∧ h ≤ min (n - 1) (2 * D)

/-- `A_k(h)` of Lemma `lem:apex`: `⌊(k-1)h/2⌋`, except `A_k(2D) = (k-1)D - 1` when `k` is even
and `D` is odd. (`Int` division by `2` is floor division.) -/
def Ak (k D h : ℤ) : ℤ :=
  if h = 2 * D ∧ k % 2 = 0 ∧ D % 2 = 1 then (k - 1) * D - 1 else (k - 1) * h / 2

/-- `p_k(h) = 3(k-1)h - 6A_k(h)`, the bracket term of Lemmas `lem:commonnbr` and
`lem:density`. -/
def pk (k D h : ℤ) : ℤ := 3 * (k - 1) * h - 6 * Ak k D h

/-- `p_k ≥ 0`, which is why the bracket may be dropped (text after `eq:apex6`). -/
theorem pk_nonneg (k D h : ℤ) : 0 ≤ pk k D h := by
  unfold pk Ak
  split_ifs with hc
  · obtain ⟨rfl, -, -⟩ := hc
    nlinarith
  · have h1 := Int.emod_add_mul_ediv ((k - 1) * h) 2
    have h2 := Int.emod_nonneg ((k - 1) * h) (by norm_num : (2 : ℤ) ≠ 0)
    nlinarith

/-- The values of `p_k` stated after Lemma `lem:apex`, at the three `(k, D)` used in Section
`sec:three`: for even `k = 6` (`D = 17` odd), `p_6(h) = 3` at odd `h`, `p_6(2D) = 6`, and `0`
otherwise on `0 ≤ h ≤ 2D`; for odd `k = 7` (`D = 22`), `p_7 = 0` on `0 ≤ h ≤ 2D`; and for even
`k = 8` (`D = 27` odd), `p_8(2D) = 6`. -/
theorem pk_values :
    (∀ h : Fin 35, pk 6 17 h.val = if h.val % 2 = 1 then 3 else if h.val = 34 then 6 else 0) ∧
    (∀ h : Fin 45, pk 7 22 h.val = 0) ∧ pk 8 27 54 = 6 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide⟩

/-- Bridge from the colour-degree caps of Lemma `lem:caps` to admissibility ("thus every `h_v`
is admissible"): if `d₁ + d₂ + d₃ = n - 1`, with `0 ≤ d_i`, `d₁, d₂ ≤ D` and `d₃ ≤ D₃`, then
`h = d₁ + d₂` is admissible. -/
theorem admissible_of_caps (n D D3 d1 d2 d3 : ℤ) (hs : d1 + d2 + d3 = n - 1)
    (h0 : 0 ≤ d1) (h0' : 0 ≤ d2) (h0'' : 0 ≤ d3) (h1 : d1 ≤ D) (h2 : d2 ≤ D) (h3 : d3 ≤ D3) :
    Admissible n D D3 (d1 + d2) := by
  unfold Admissible
  simp only [le_min_iff, max_le_iff]
  omega

/-- The function `F = F_{n,k,U}` of Lemma `lem:commonnbr`, without the bracket. -/
def Fcn (n k U h : ℤ) : ℤ := 3 * h ^ 2 + (U + 5 - 3 * n - 3 * k) * h + (n - U - 1) * (n - 1)

/-- Step 4 of the proof of Lemma `lem:commonnbr` (collecting terms): with `z = n-1-h`,
`h(h-1) - (3(k-1)h - p + 2hz + (U+1-n)z) = F(h) + p`. -/
theorem commonnbr_collect (n k U h p : ℤ) :
    h * (h - 1) - (3 * (k - 1) * h - p + 2 * h * (n - 1 - h) + (U + 1 - n) * (n - 1 - h))
      = Fcn n k U h + p := by
  unfold Fcn; ring

/-- The function `Psi = Psi_{n,k}` of Lemma `lem:density`, without the bracket, for a chosen
lower-bound function `m = m_{k-1}`. -/
def Psi (n k : ℤ) (m : ℤ → ℤ) (h : ℤ) : ℤ := h * (2 * h - n - 3 * (k - 1)) + 2 * m (n - 1 - h)

/-- Step 3 of the proof of Lemma `lem:density`: comparing `6T(H) ≥ h(2h-n) + 2m` with the
apex bound `6T(H) ≤ 3(k-1)h - p` gives `Psi + p`. -/
theorem density_collect (n k h mz p : ℤ) (m : ℤ → ℤ) (hm : m (n - 1 - h) = mz) :
    h * (2 * h - n) + 2 * mz - (3 * (k - 1) * h - p) = Psi n k m h + p := by
  unfold Psi; rw [hm]; ring

/-! ## Theorem `thm:336`: `R(3,3,6) ≤ 88`

Ramsey inputs: `D = R(3,6) - 1 = 17` (the red and blue caps, so `h ≤ 34`) and
`U = R(3,3,4) = 30` in Lemma `lem:commonnbr`. -/

/-- Step 2 of `thm:336`: `F_{88,6,30}(h) = 3h² - 247h + 4959`. -/
theorem thm336_F_eq (h : ℤ) : Fcn 88 6 30 h = 3 * h ^ 2 - 247 * h + 4959 := by
  unfold Fcn; ring

/-- Step 3 of `thm:336`: with `x = 34 - h`, `F = 29 + 43x + 3x²`. -/
theorem thm336_F_shift (x : ℤ) : Fcn 88 6 30 (34 - x) = 29 + 43 * x + 3 * x ^ 2 := by
  unfold Fcn; ring

/-- Step 3 of `thm:336`: `F_{88,6,30}(h) > 0` for every integer `h ≤ 34`. -/
theorem thm336_F_pos (h : ℤ) (hh : h ≤ 34) : 0 < Fcn 88 6 30 h := by
  have := thm336_F_shift (34 - h)
  rw [show 34 - (34 - h) = h by ring] at this
  rw [this]
  nlinarith

/-- In particular `F_{88,6,30} > 0` at every admissible `h` (for any green cap `D₃`),
with `D = 17`. -/
theorem thm336_F_pos_adm (D3 h : ℤ) (hh : Admissible 88 17 D3 h) : 0 < Fcn 88 6 30 h :=
  thm336_F_pos h (le_trans hh.2 (min_le_right _ _))

/-- Theorem `thm:336`, step (iii) with Lemma `lem:line`(b): there is no nonempty vertex set
with red and blue degrees `r v, b v ≤ 17` (`D = R(3,6)-1`) and `∑_v F_{88,6,30}(h_v) ≤ 0`
(Lemma `lem:commonnbr` with `n = 88`, `k = 6`, `U = 30`), where `h_v = r v + b v`. -/
theorem thm336_contradiction {V : Type*} [Fintype V] [Nonempty V] (r b : V → ℤ)
    (hr : ∀ v, r v ≤ 17) (hb : ∀ v, b v ≤ 17)
    (hsum : ∑ v, Fcn 88 6 30 (r v + b v) ≤ 0) : False := by
  have := line_b (Fcn 88 6 30) (fun x => x ≤ 34) (fun x hx => thm336_F_pos x hx)
    (fun v => r v + b v) (fun v => by have := hr v; have := hb v; simp only; omega)
  exact absurd hsum (not_le.mpr this)

/-- "Why the argument stops here": `F_{87,6,30}(h) = 3h² - 244h + 4816`. -/
theorem thm336_stop_F_eq (h : ℤ) : Fcn 87 6 30 h = 3 * h ^ 2 - 244 * h + 4816 := by
  unfold Fcn; ring

/-- "Why the argument stops here": `F_{87,6,30}(34) = -12`, `p_6(34) = 6` (as `34 = 2D`
with `D = 17` odd), so `-6` with the bracket, and `h = 34` is admissible at `n = 87` under the
green cap `D₃ = 56`. -/
theorem thm336_stop :
    Fcn 87 6 30 34 = -12 ∧ pk 6 17 34 = 6 ∧ Fcn 87 6 30 34 + pk 6 17 34 = -6 ∧
      Admissible 87 17 56 34 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  unfold Admissible; norm_num

/-! ## Lemma `lem:m6more`: the bounds `m₆(z)` for `79 ≤ z ≤ 87` (display `eq:chord`) -/

/-- `F_{z,6,30}(h) = 3h² - (3z-17)h + (z-31)(z-1)`. -/
theorem F6_eq (z h : ℤ) : Fcn z 6 30 h = 3 * h ^ 2 - (3 * z - 17) * h + (z - 31) * (z - 1) := by
  unfold Fcn; ring

/-- `β = 3z - 20 - 6q` of `eq:chord`. -/
def beta6 (z q : ℤ) : ℤ := 3 * z - 20 - 6 * q

/-- `α = (z-31)(z-1) - 3q(q+1)` of `eq:chord`. -/
def alpha6 (z q : ℤ) : ℤ := (z - 31) * (z - 1) - 3 * q * (q + 1)

/-- The identity of display `eq:chord`:
`F_{z,6,30}(h) = α - βh + 3(h-q)(h-q-1)`. -/
theorem chord_identity (z q h : ℤ) :
    Fcn z 6 30 h = alpha6 z q - beta6 z q * h + 3 * (h - q) * (h - q - 1) := by
  unfold Fcn alpha6 beta6; ring

/-- A product of two consecutive integers is nonnegative. -/
theorem consecutive_mul_nonneg (a : ℤ) : 0 ≤ a * (a - 1) := by
  rcases le_or_gt a 0 with h | h
  · nlinarith
  · nlinarith

/-- The inequality of display `eq:chord`: `F_{z,6,30}(h) ≥ α - βh` at every integer `h`. -/
theorem chord_le (z q h : ℤ) : alpha6 z q - beta6 z q * h ≤ Fcn z 6 30 h := by
  rw [chord_identity]
  nlinarith [consecutive_mul_nonneg (h - q)]

/-- The column `q` of the table of Lemma `lem:m6more`. -/
def q6 (z : ℤ) : ℤ :=
  if z = 79 then 26 else if z = 80 then 27 else if z = 81 then 28 else if z = 82 then 29
  else if z = 83 then 30 else if z = 84 then 30 else if z = 85 then 31 else if z = 86 then 32
  else if z = 87 then 33 else 0

/-- The row `m₆(z)` of the table of Lemma `lem:m6more`. -/
def m6 (z : ℤ) : ℤ :=
  if z = 79 then 1061 else if z = 80 then 1106 else if z = 81 then 1152
  else if z = 82 then 1200 else if z = 83 then 1249 else if z = 84 then 1300
  else if z = 85 then 1354 else if z = 86 then 1409 else if z = 87 then 1467 else 0

/-- The rows `β` and `α` of the table of Lemma `lem:m6more`. -/
theorem m6_table_beta_alpha :
    (beta6 79 (q6 79), alpha6 79 (q6 79)) = (61, 1638) ∧
    (beta6 80 (q6 80), alpha6 80 (q6 80)) = (58, 1603) ∧
    (beta6 81 (q6 81), alpha6 81 (q6 81)) = (55, 1564) ∧
    (beta6 82 (q6 82), alpha6 82 (q6 82)) = (52, 1521) ∧
    (beta6 83 (q6 83), alpha6 83 (q6 83)) = (49, 1474) ∧
    (beta6 84 (q6 84), alpha6 84 (q6 84)) = (52, 1609) ∧
    (beta6 85 (q6 85), alpha6 85 (q6 85)) = (49, 1560) ∧
    (beta6 86 (q6 86), alpha6 86 (q6 86)) = (46, 1507) ∧
    (beta6 87 (q6 87), alpha6 87 (q6 87)) = (43, 1450) := by
  decide +kernel

/-- Every `β` in the table is positive (proof of Lemma `lem:m6more`). -/
theorem m6_beta_pos (z : ℤ) (h1 : 79 ≤ z) (h2 : z ≤ 87) : 0 < beta6 z (q6 z) := by
  interval_cases z <;> decide

/-- `q = ⌊r⌋` for the smaller root `r` of `F_{z,6,30}`: `F(q) > 0 > F(q+1)`, so the convex
quadratic `F` has its smaller root strictly between `q` and `q+1`. -/
theorem m6_q_floor_root (z : ℤ) (h1 : 79 ≤ z) (h2 : z ≤ 87) :
    0 < Fcn z 6 30 (q6 z) ∧ Fcn z 6 30 (q6 z + 1) < 0 := by
  interval_cases z <;> decide

/-- The row `r` of the table, rounded to two decimals: `F_{z,6,30}` changes sign from positive
to negative between `r̃ - 1/200` and `r̃ + 1/200`, where `r̃` is the tabulated value. Since `F` is
a convex quadratic, its smaller root lies in that interval and so rounds to `r̃`. -/
theorem m6_root_rounding :
    let F : ℚ → ℚ → ℚ := fun z h => 3 * h ^ 2 - (3 * z - 17) * h + (z - 31) * (z - 1)
    (0 < F 79 (26.85 - 0.005) ∧ F 79 (26.85 + 0.005) < 0) ∧
    (0 < F 80 (27.63 - 0.005) ∧ F 80 (27.63 + 0.005) < 0) ∧
    (0 < F 81 (28.42 - 0.005) ∧ F 81 (28.42 + 0.005) < 0) ∧
    (0 < F 82 (29.24 - 0.005) ∧ F 82 (29.24 + 0.005) < 0) ∧
    (0 < F 83 (30.08 - 0.005) ∧ F 83 (30.08 + 0.005) < 0) ∧
    (0 < F 84 (30.94 - 0.005) ∧ F 84 (30.94 + 0.005) < 0) ∧
    (0 < F 85 (31.83 - 0.005) ∧ F 85 (31.83 + 0.005) < 0) ∧
    (0 < F 86 (32.75 - 0.005) ∧ F 86 (32.75 + 0.005) < 0) ∧
    (0 < F 87 (33.71 - 0.005) ∧ F 87 (33.71 + 0.005) < 0) := by
  norm_num

/-- The discriminant `(3z-17)² - 12(z-31)(z-1)` of `F_{z,6,30}`. -/
def disc6 (z : ℤ) : ℤ := (3 * z - 17) ^ 2 - 12 * (z - 31) * (z - 1)

/-- The discriminant decreases from `3472` to `1744` on `79 ≤ z ≤ 87` and is never a perfect
square there, so `r` is never an integer. -/
theorem m6_disc :
    disc6 79 = 3472 ∧ disc6 87 = 1744 ∧
    (∀ z : ℤ, 79 ≤ z → z < 87 → disc6 (z + 1) < disc6 z) ∧
    (∀ z : ℤ, 79 ≤ z → z ≤ 87 → ∀ s : ℤ, s ^ 2 ≠ disc6 z) := by
  refine ⟨by decide, by decide, fun z h1 h2 => ?_, fun z h1 h2 s => ?_⟩
  · unfold disc6; nlinarith
  · have hd : disc6 z ≤ 3472 := by
      interval_cases z <;> decide
    have key : ∀ t : ℕ, t < 59 → (t : ℤ) ^ 2 ≠ disc6 z := by
      interval_cases z <;> decide +kernel
    intro hs
    have habs : |s| < 59 := abs_lt_of_sq_lt_sq (by linarith) (by norm_num)
    obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = |s| := ⟨|s|.toNat, Int.toNat_of_nonneg (abs_nonneg s)⟩
    exact key t (by omega) (by rw [ht, sq_abs]; exact hs)

/-- The row `m₆(z) = ⌈zα/(2β)⌉` of the table of Lemma `lem:m6more`. -/
theorem m6_ceil (z : ℤ) (h1 : 79 ≤ z) (h2 : z ≤ 87) :
    m6 z = ⌈((z * alpha6 z (q6 z) : ℤ) : ℚ) / ((2 * beta6 z (q6 z) : ℤ) : ℚ)⌉ := by
  rw [eq_comm, Int.ceil_eq_iff]
  interval_cases z <;> norm_num [m6, q6, alpha6, beta6]

/-- The same rounding in integer form: `2β(m₆ - 1) < zα ≤ 2β m₆`. -/
theorem m6_ceil_int (z : ℤ) (h1 : 79 ≤ z) (h2 : z ≤ 87) :
    2 * beta6 z (q6 z) * (m6 z - 1) < z * alpha6 z (q6 z) ∧
      z * alpha6 z (q6 z) ≤ 2 * beta6 z (q6 z) * m6 z := by
  interval_cases z <;> decide

/-- Lemma `lem:m6more`: for `79 ≤ z ≤ 87`, if a vertex set of size `z` with `H`-degrees `h_v`
satisfies `∑_v F_{z,6,30}(h_v) ≤ 0` (Lemma `lem:commonnbr` for `(3,3,6;z)`-colourings, with
`U = R(3,3,4) = 30`) and `2E = ∑_v h_v`, then `E ≥ m₆(z)`. No degree cap is needed, as the
chord inequality holds at every integer. -/
theorem lem_m6more {V : Type*} [Fintype V] (z : ℤ) (hz1 : 79 ≤ z) (hz2 : z ≤ 87)
    (hcard : (Fintype.card V : ℤ) = z) (h : V → ℤ) (hsum : ∑ v, Fcn z 6 30 (h v) ≤ 0)
    (E : ℤ) (hE : 2 * E = ∑ v, h v) : m6 z ≤ E := by
  apply line_a_ceil (Fcn z 6 30) (fun _ => True) (alpha6 z (q6 z)) (beta6 z (q6 z)) (m6 z)
    (m6_beta_pos z hz1 hz2) (fun x _ => chord_le z (q6 z) x) h (fun _ => trivial) hsum E hE
  rw [hcard]
  exact (m6_ceil_int z hz1 hz2).1

/-! ## Theorem `thm:337`: `R(3,3,7) ≤ 129`

Ramsey inputs: `D = R(3,7) - 1 = 22`, the green cap `D₃ = 87` from `R(3,3,6) ≤ 88`
(Theorem `thm:336`), and the valid lower bounds `m₆(z)` of Lemma `lem:m6more`. -/

/-- Step 1 of `thm:337`: the admissible `H`-degrees are `41, …, 44`. -/
theorem thm337_admissible (h : ℤ) : Admissible 129 22 87 h ↔ 41 ≤ h ∧ h ≤ 44 := by
  unfold Admissible; constructor <;> intro hh <;> simp only [le_min_iff, max_le_iff] at * <;>
    omega

/-- Step 2 of `thm:337`: `Psi(h) = h(2h-147) + 2m₆(128-h)`. -/
theorem thm337_Psi_eq (h : ℤ) : Psi 129 7 m6 h = h * (2 * h - 147) + 2 * m6 (128 - h) := by
  unfold Psi; ring_nf

/-- The table of Step 3 of `thm:337`: `(h, z, m₆(z), Psi(h))`. -/
theorem thm337_table :
    (m6 87, Psi 129 7 m6 41) = (1467, 269) ∧ (m6 86, Psi 129 7 m6 42) = (1409, 172) ∧
    (m6 85, Psi 129 7 m6 43) = (1354, 85) ∧ (m6 84, Psi 129 7 m6 44) = (1300, 4) := by
  decide +kernel

/-- Step 3 of `thm:337`: `Psi > 0` at every admissible `h`. -/
theorem thm337_Psi_pos (h : ℤ) (hh : Admissible 129 22 87 h) : 0 < Psi 129 7 m6 h := by
  obtain ⟨h1, h2⟩ := (thm337_admissible h).1 hh
  interval_cases h <;> decide

/-- Theorem `thm:337`, step (iii): no nonempty vertex set has all `H`-degrees admissible
(red, blue caps `22`, green cap `87`) and `∑_v Psi(h_v) ≤ 0` (Lemma `lem:density` with
`n = 129`, `k = 7` and the bounds `m₆` of Lemma `lem:m6more`). -/
theorem thm337_contradiction {V : Type*} [Fintype V] [Nonempty V] (h : V → ℤ)
    (hadm : ∀ v, Admissible 129 22 87 (h v)) (hsum : ∑ v, Psi 129 7 m6 (h v) ≤ 0) : False := by
  have := line_b (Psi 129 7 m6) (Admissible 129 22 87) thm337_Psi_pos h hadm
  omega

/-- Theorem `thm:337` with the caps as hypotheses: no nonempty vertex set has colour degrees
`r v, b v ≤ 22` (`R(3,7) = 23`), `g v ≤ 87` (`R(3,3,6) ≤ 88`), `r v + b v + g v = 128`, and
`Σ_v Psi(r v + b v) ≤ 0`. -/
theorem thm337_contradiction_caps {V : Type*} [Fintype V] [Nonempty V] (r b g : V → ℕ)
    (hs : ∀ v, r v + b v + g v = 128) (hr : ∀ v, r v ≤ 22) (hb : ∀ v, b v ≤ 22)
    (hg : ∀ v, g v ≤ 87) (hsum : ∑ v, Psi 129 7 m6 ((r v : ℤ) + b v) ≤ 0) : False :=
  thm337_contradiction (fun v => (r v : ℤ) + b v)
    (fun v => admissible_of_caps 129 22 87 (r v) (b v) (g v) (by have := hs v; push_cast; omega)
      (by positivity) (by positivity) (by positivity) (by have := hr v; omega)
      (by have := hb v; omega) (by have := hg v; omega)) hsum

/-- "Comparison" after `thm:337`: Lemma `lem:commonnbr` with `U = 57` gives
`F = 3h² - 346h + 9088`, negative at every admissible `h` (largest value `F(41) = -55`); and
`Psi` with the trivial `m₆ = 0` is negative at every admissible `h`; and by contrast the bounds
`m₆(z)` give average red-or-blue degree `2m₆(z)/z > 30` for `84 ≤ z ≤ 87`. -/
theorem thm337_comparison :
    (∀ h, Fcn 129 7 57 h = 3 * h ^ 2 - 346 * h + 9088) ∧ Fcn 129 7 57 41 = -55 ∧
    (∀ h, Admissible 129 22 87 h → Fcn 129 7 57 h ≤ -55) ∧
    (∀ h, Admissible 129 22 87 h → Psi 129 7 (fun _ => 0) h < 0) ∧
    (∀ z : ℤ, 84 ≤ z → z ≤ 87 → 30 * z < 2 * m6 z) := by
  refine ⟨fun h => by unfold Fcn; ring, by decide, fun h hh => ?_, fun h hh => ?_,
    fun z h1 h2 => ?_⟩
  · obtain ⟨h1, h2⟩ := (thm337_admissible h).1 hh
    interval_cases h <;> decide
  · obtain ⟨h1, h2⟩ := (thm337_admissible h).1 hh
    interval_cases h <;> decide
  · interval_cases z <;> decide

/-! ## Lemma `lem:m7`: the bounds `m₇(z)` for `124 ≤ z ≤ 128`

Ramsey inputs: `D = R(3,7) - 1 = 22`, the green cap `87` from `R(3,3,6) ≤ 88`, the bounds `m₆`
of Lemma `lem:m6more`, and `R(3,3,6) ≤ 88` again in Lemma `lem:delete`(a). -/

/-- Step 1 of `lem:m7`: at `n = 124` the admissible `H`-degrees are `36, …, 44`. -/
theorem m7_admissible (h : ℤ) : Admissible 124 22 87 h ↔ 36 ≤ h ∧ h ≤ 44 := by
  unfold Admissible; constructor <;> intro hh <;> simp only [le_min_iff, max_le_iff] at * <;>
    omega

/-- Step 2 of `lem:m7`: `Psi(h) = h(2h-142) + 2m₆(123-h)`. -/
theorem m7_Psi_eq (h : ℤ) : Psi 124 7 m6 h = h * (2 * h - 142) + 2 * m6 (123 - h) := by
  unfold Psi; ring_nf

/-- The table of Step 3 of `lem:m7`: the values `Psi(h)` and `Psi(h) - (3138 - 78h)`
for `h = 36, …, 44`. -/
theorem m7_table :
    [36, 37, 38, 39, 40, 41, 42, 43, 44].map (Psi 124 7 m6) =
      [414, 302, 200, 104, 18, -60, -132, -196, -254] ∧
    [36, 37, 38, 39, 40, 41, 42, 43, 44].map (fun h => Psi 124 7 m6 h - (3138 - 78 * h)) =
      [84, 50, 26, 8, 0, 0, 6, 20, 40] := by
  decide +kernel

/-- Step 3 of `lem:m7`: `Psi(h) ≥ 3138 - 78h` at every admissible `h`. -/
theorem m7_chord (h : ℤ) (hh : Admissible 124 22 87 h) : 3138 - 78 * h ≤ Psi 124 7 m6 h := by
  obtain ⟨h1, h2⟩ := (m7_admissible h).1 hh
  interval_cases h <;> decide

/-- Step 3 of `lem:m7`, the rounding: `124 · 3138 / 156 > 2494`, and `⌈124 · 3138/156⌉ = 2495`. -/
theorem m7_round : 2494 * 156 < 124 * 3138 ∧ 124 * 3138 ≤ 2495 * 156 := by norm_num

/-- Lemma `lem:m7` at `z = 124`: a vertex set of size `124` with all `H`-degrees admissible
(caps `22`, `22`, `87`), `∑_v Psi(h_v) ≤ 0` (Lemma `lem:density` with `n = 124`, `k = 7`, `m₆`)
and `2E = ∑_v h_v` has `E ≥ 2495`. -/
theorem lem_m7_124 {V : Type*} [Fintype V] (hcard : Fintype.card V = 124) (h : V → ℤ)
    (hadm : ∀ v, Admissible 124 22 87 (h v)) (hsum : ∑ v, Psi 124 7 m6 (h v) ≤ 0)
    (E : ℤ) (hE : 2 * E = ∑ v, h v) : 2495 ≤ E := by
  apply line_a_ceil (Psi 124 7 m6) (Admissible 124 22 87) 3138 78 2495 (by norm_num)
    m7_chord h hadm hsum E hE
  rw [hcard]; norm_num

/-- The values of Lemma `lem:m7`. -/
def m7 (z : ℤ) : ℤ :=
  if z = 124 then 2495 else if z = 125 then 2532 else if z = 126 then 2570
  else if z = 127 then 2609 else if z = 128 then 2649 else 0

/-- Step 4 of `lem:m7`: `m₇(z) = m₇(z-1) + (z - 88)` for `125 ≤ z ≤ 128`, the increment
`max(0, z - R(3,3,6))` of Lemma `lem:delete`(a) with `R(3,3,6) ≤ 88`. -/
theorem m7_step (z : ℤ) (h1 : 125 ≤ z) (h2 : z ≤ 128) :
    m7 z = m7 (z - 1) + max 0 (z - 88) := by
  interval_cases z <;> decide

/-! ## Theorem `thm:338`: `R(3,3,8) ≤ 179`

Ramsey inputs: `D = R(3,8) - 1 = 27`, the green cap `128` from `R(3,3,7) ≤ 129`
(Theorem `thm:337`), and the bounds `m₇` of Lemma `lem:m7`. -/

/-- Step 1 of `thm:338`: the admissible `H`-degrees are `50, …, 54`. -/
theorem thm338_admissible (h : ℤ) : Admissible 179 27 128 h ↔ 50 ≤ h ∧ h ≤ 54 := by
  unfold Admissible; constructor <;> intro hh <;> simp only [le_min_iff, max_le_iff] at * <;>
    omega

/-- Step 2 of `thm:338`: `Psi(h) = h(2h-200) + 2m₇(178-h)`. -/
theorem thm338_Psi_eq (h : ℤ) : Psi 179 8 m7 h = h * (2 * h - 200) + 2 * m7 (178 - h) := by
  unfold Psi; ring_nf

/-- The table of Step 3 of `thm:338`: `(m₇(z), Psi(h))` for `h = 50, …, 54`. -/
theorem thm338_table :
    (m7 128, Psi 179 8 m7 50) = (2649, 298) ∧ (m7 127, Psi 179 8 m7 51) = (2609, 220) ∧
    (m7 126, Psi 179 8 m7 52) = (2570, 148) ∧ (m7 125, Psi 179 8 m7 53) = (2532, 82) ∧
    (m7 124, Psi 179 8 m7 54) = (2495, 22) := by
  decide +kernel

/-- Step 3 of `thm:338`: `Psi > 0` at every admissible `h`. -/
theorem thm338_Psi_pos (h : ℤ) (hh : Admissible 179 27 128 h) : 0 < Psi 179 8 m7 h := by
  obtain ⟨h1, h2⟩ := (thm338_admissible h).1 hh
  interval_cases h <;> decide

/-- Theorem `thm:338`, step (iii): no nonempty vertex set has all `H`-degrees admissible
(caps `27`, `27`, `128`) and `∑_v Psi(h_v) ≤ 0` (Lemma `lem:density` with `n = 179`, `k = 8`
and the bounds `m₇`). -/
theorem thm338_contradiction {V : Type*} [Fintype V] [Nonempty V] (h : V → ℤ)
    (hadm : ∀ v, Admissible 179 27 128 (h v)) (hsum : ∑ v, Psi 179 8 m7 (h v) ≤ 0) : False := by
  have := line_b (Psi 179 8 m7) (Admissible 179 27 128) thm338_Psi_pos h hadm
  omega


/-- Theorem `thm:338` with the caps as hypotheses: no nonempty vertex set has colour degrees
`r v, b v ≤ 27` (`R(3,8) = 28`), `g v ≤ 128` (`R(3,3,7) ≤ 129`), `r v + b v + g v = 178`, and
`Σ_v Psi(r v + b v) ≤ 0`. -/
theorem thm338_contradiction_caps {V : Type*} [Fintype V] [Nonempty V] (r b g : V → ℕ)
    (hs : ∀ v, r v + b v + g v = 178) (hr : ∀ v, r v ≤ 27) (hb : ∀ v, b v ≤ 27)
    (hg : ∀ v, g v ≤ 128) (hsum : ∑ v, Psi 179 8 m7 ((r v : ℤ) + b v) ≤ 0) : False :=
  thm338_contradiction (fun v => (r v : ℤ) + b v)
    (fun v => admissible_of_caps 179 27 128 (r v) (b v) (g v) (by have := hs v; push_cast; omega)
      (by positivity) (by positivity) (by positivity) (by have := hr v; omega)
      (by have := hb v; omega) (by have := hg v; omega)) hsum

/-- Lemma `lem:m7` at `z = 124` with the caps as hypotheses (`r v, b v ≤ 22`, `g v ≤ 87`,
`r v + b v + g v = 123`). -/
theorem lem_m7_124_caps {V : Type*} [Fintype V] (hcard : Fintype.card V = 124) (r b g : V → ℕ)
    (hs : ∀ v, r v + b v + g v = 123) (hr : ∀ v, r v ≤ 22) (hb : ∀ v, b v ≤ 22)
    (hg : ∀ v, g v ≤ 87) (hsum : ∑ v, Psi 124 7 m6 ((r v : ℤ) + b v) ≤ 0)
    (E : ℤ) (hE : 2 * E = ∑ v, ((r v : ℤ) + b v)) : 2495 ≤ E :=
  lem_m7_124 hcard (fun v => (r v : ℤ) + b v)
    (fun v => admissible_of_caps 124 22 87 (r v) (b v) (g v) (by have := hs v; push_cast; omega)
      (by positivity) (by positivity) (by positivity) (by have := hr v; omega)
      (by have := hb v; omega) (by have := hg v; omega)) hsum E hE

/-! ## Section `sec:types`: the weighted triangle identities

The paper's `Phi` is defined from six real weights and the mixed caps `C_ij`. We define it in
that generality (`PhiGen`), with the floors (`PhiFl`) and without them (`PhiFF`), and then show
that each explicit integer polynomial used below is the paper's `Phi` for the stated weights and
caps. Caps of types whose coefficient vanishes are left as arbitrary parameters, as the paper
says that such types "need no cap". -/

/-- `binom(d, 2) = d(d-1)/2`, over `ℚ`. -/
def ch2 (d : ℚ) : ℚ := d * (d - 1) / 2

/-- Six weights `(w₁, w₂, w₃; w₁₂, w₁₃, w₂₃)` of Lemma `lem:weighted`. -/
structure Weights where
  w1 : ℚ
  w2 : ℚ
  w3 : ℚ
  w12 : ℚ
  w13 : ℚ
  w23 : ℚ

namespace Weights

variable (w : Weights)

/-- `W(d) = Σ_i w_i binom(d_i,2) + Σ_{i<j} w_ij d_i d_j` of Lemma `lem:weighted`, at
`d = (r, b, g)`. -/
def W (r b g : ℚ) : ℚ :=
  w.w1 * ch2 r + w.w2 * ch2 b + w.w3 * ch2 g + w.w12 * r * b + w.w13 * r * g + w.w23 * b * g

/-- Coefficients `w_i + 2w_ij` of `T_{i,j}` in Lemma `lem:weighted` (with `w_ji = w_ij`). -/
def cT12 : ℚ := w.w1 + 2 * w.w12
def cT13 : ℚ := w.w1 + 2 * w.w13
def cT21 : ℚ := w.w2 + 2 * w.w12
def cT23 : ℚ := w.w2 + 2 * w.w23
def cT31 : ℚ := w.w3 + 2 * w.w13
def cT32 : ℚ := w.w3 + 2 * w.w23
/-- Coefficient `w₁₂ + w₁₃ + w₂₃` of `X` in Lemma `lem:weighted`. -/
def cX : ℚ := w.w12 + w.w13 + w.w23

/-- The sign conditions of Section `sec:types`. -/
def SignConditions : Prop :=
  w.cX = 0 ∧ 0 ≤ w.w2 ∧ 0 ≤ w.w3 ∧ 0 ≤ w.cT12 ∧ 0 ≤ w.cT13 ∧ 0 ≤ w.cT21 ∧ 0 ≤ w.cT23 ∧
    0 ≤ w.cT31 ∧ 0 ≤ w.cT32

end Weights

/-- Mixed caps `C_ij` (Lemma `lem:caps`); `C_ij` caps colour-`j` neighbours inside a
colour-`i` neighbourhood, and multiplies `d_i`. -/
structure Caps where
  c12 : ℤ
  c13 : ℤ
  c21 : ℤ
  c23 : ℤ
  c31 : ℤ
  c32 : ℤ
  c22 : ℤ
  c33 : ℤ

/-- `Phi(d) = W(d) - Σ_{i=2,3} w_i ρ(C_ii d_i/2) - Σ_{i≠j} (w_i+2w_ij) ρ(C_ij d_i/2)`, where
`ρ` is the floor (`PhiFl`) or the identity (`PhiFF`, the floor-free form). -/
def PhiGen (ρ : ℚ → ℚ) (w : Weights) (c : Caps) (r b g : ℤ) : ℚ :=
  w.W r b g - w.w2 * ρ (c.c22 * b / 2) - w.w3 * ρ (c.c33 * g / 2)
    - w.cT12 * ρ (c.c12 * r / 2) - w.cT13 * ρ (c.c13 * r / 2)
    - w.cT21 * ρ (c.c21 * b / 2) - w.cT23 * ρ (c.c23 * b / 2)
    - w.cT31 * ρ (c.c31 * g / 2) - w.cT32 * ρ (c.c32 * g / 2)

/-- `Phi` with the floors. -/
def PhiFl (w : Weights) (c : Caps) (r b g : ℤ) : ℚ := PhiGen (fun x => (⌊x⌋ : ℚ)) w c r b g

/-- The floor-free form of `Phi`. -/
def PhiFF (w : Weights) (c : Caps) (r b g : ℤ) : ℚ := PhiGen id w c r b g

/-- "Dropping the floors only lowers `Phi`" (Section `sec:types`), under the sign conditions. -/
theorem PhiFF_le_PhiFl (w : Weights) (hw : w.SignConditions) (c : Caps) (r b g : ℤ) :
    PhiFF w c r b g ≤ PhiFl w c r b g := by
  obtain ⟨-, h2, h3, h12, h13, h21, h23, h31, h32⟩ := hw
  unfold PhiFF PhiFl PhiGen
  simp only [id]
  have k := fun (a x : ℚ) (ha : 0 ≤ a) => mul_le_mul_of_nonneg_left (Int.floor_le x) ha
  linarith [k _ (c.c22 * b / 2) h2, k _ (c.c33 * g / 2) h3, k _ (c.c12 * r / 2) h12,
    k _ (c.c13 * r / 2) h13, k _ (c.c21 * b / 2) h21, k _ (c.c23 * b / 2) h23,
    k _ (c.c31 * g / 2) h31, k _ (c.c32 * g / 2) h32]

/-- For integers, `⌊c d / 2⌋` is integer floor division. -/
theorem floor_half (c d : ℤ) : ⌊(c : ℚ) * d / 2⌋ = c * d / 2 := by
  have := Rat.floor_intCast_div_natCast (c * d) 2
  push_cast at this
  exact this

/-! ### Theorem `thm:345`: `R(3,4,5) ≤ 155`

Ramsey inputs: `r ≤ D₁ = R(4,5) - 1 = 24`, `b ≤ D₂ ≤ 56` from `R(3,3,5) ≤ 57`, and the mixed
caps `C₁₂ = R(3,5) - 1 = 13`, `C₂₂ = 13`, `C₂₃ = C₃₂ = C₃₃ = R(3,3,4) - 1 = 29`. -/

/-- The weights `(2γ, 2α, 2γ; -α, -γ, α+γ)` of the proof of `thm:345`. -/
def wAG (α γ : ℚ) : Weights := ⟨2 * γ, 2 * α, 2 * γ, -α, -γ, α + γ⟩

/-- The caps of `thm:345`; `c13`, `c21`, `c31` multiply vanishing coefficients. -/
def caps345 (c13 c21 c31 : ℤ) : Caps := ⟨13, c13, c21, 29, c31, 29, 13, 29⟩

/-- "Choosing which types vanish": these weights kill `X`, `T₁₃`, `T₂₁`, `T₃₁`, and leave
`Σ_v W = 2(γ-α)T₁₂ + (4α+2γ)T₂₃ + (2α+4γ)T₃₂ + 2α·3M₂ + 2γ·3M₃`. -/
theorem wAG_coeffs (α γ : ℚ) :
    (wAG α γ).cX = 0 ∧ (wAG α γ).cT13 = 0 ∧ (wAG α γ).cT21 = 0 ∧ (wAG α γ).cT31 = 0 ∧
    (wAG α γ).cT12 = 2 * (γ - α) ∧ (wAG α γ).cT23 = 4 * α + 2 * γ ∧
    (wAG α γ).cT32 = 2 * α + 4 * γ ∧ (wAG α γ).w2 = 2 * α ∧ (wAG α γ).w3 = 2 * γ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [wAG, Weights.cX, Weights.cT12, Weights.cT13, Weights.cT21, Weights.cT23,
      Weights.cT31, Weights.cT32] <;> ring

/-- "The sign conditions hold exactly when `γ ≥ α ≥ 0`." -/
theorem wAG_sign_iff (α γ : ℚ) : (wAG α γ).SignConditions ↔ α ≤ γ ∧ 0 ≤ α := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := wAG_coeffs α γ
  simp only [Weights.SignConditions, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  constructor
  · rintro ⟨-, ha, -, hga, -⟩; constructor <;> linarith
  · rintro ⟨hag, ha⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | exact le_rfl | linarith

/-- "Capping the surviving types": the floor-free `Phi` is
`W - 13(γ-α)r - (71α+29γ)b - (29α+87γ)g`. -/
theorem thm345_PhiFF_general (α γ : ℚ) (c13 c21 c31 r b g : ℤ) :
    PhiFF (wAG α γ) (caps345 c13 c21 c31) r b g =
      (wAG α γ).W r b g - 13 * (γ - α) * r - (71 * α + 29 * γ) * b - (29 * α + 87 * γ) * g := by
  simp only [PhiFF, PhiGen, wAG, caps345, Weights.cT12, Weights.cT13, Weights.cT21,
    Weights.cT23, Weights.cT31, Weights.cT32, id]
  push_cast; ring

/-- "Constant term": `W(24, 56, 74) = 5880α + 8322γ`. -/
theorem thm345_W_const (α γ : ℚ) : (wAG α γ).W 24 56 74 = 5880 * α + 8322 * γ := by
  simp only [Weights.W, wAG, ch2]; ring

/-- "Reduction to two variables": with `(r,b,g) = (24-x, 56-y, 74+x+y)`,
`Phi = (70α-52γ) + (70α+132γ)x + 3γx² + (47γ-63α)y + 2(γ-α)xy`. -/
theorem thm345_reduction (α γ : ℚ) (c13 c21 c31 x y : ℤ) :
    PhiFF (wAG α γ) (caps345 c13 c21 c31) (24 - x) (56 - y) (74 + x + y) =
      (70 * α - 52 * γ) + (70 * α + 132 * γ) * x + 3 * γ * x ^ 2 + (47 * γ - 63 * α) * y
        + 2 * (γ - α) * x * y := by
  rw [thm345_PhiFF_general]
  simp only [Weights.W, wAG, ch2]
  push_cast; ring

/-- The weights `(78, 58, 78; -29, -39, 68)`, i.e. `α = 29`, `γ = 39`. -/
def w345 : Weights := ⟨78, 58, 78, -29, -39, 68⟩

theorem w345_eq : w345 = wAG 29 39 := by
  simp only [w345, wAG, Weights.mk.injEq]; norm_num

/-- `Σ_v W = 20T₁₂ + 194T₂₃ + 214T₃₂ + 58·3M₂ + 78·3M₃`: the coefficients of all ten types,
and the sign conditions. -/
theorem w345_coeffs :
    w345.cX = 0 ∧ w345.cT12 = 20 ∧ w345.cT13 = 0 ∧ w345.cT21 = 0 ∧ w345.cT23 = 194 ∧
      w345.cT31 = 0 ∧ w345.cT32 = 214 ∧ w345.w2 = 58 ∧ w345.w3 = 78 ∧ w345.SignConditions := by
  simp only [Weights.SignConditions, w345, Weights.cX, Weights.cT12, Weights.cT13,
    Weights.cT21, Weights.cT23, Weights.cT31, Weights.cT32]
  norm_num

/-- The integer polynomial `Phi = W - 130r - 3190b - 4234g` of the proof of `thm:345`. -/
def Phi345 (r b g : ℤ) : ℤ :=
  39 * r * (r - 1) + 29 * b * (b - 1) + 39 * g * (g - 1) - 29 * r * b - 39 * r * g
    + 68 * b * g - 130 * r - 3190 * b - 4234 * g

/-- `Phi345` is the paper's floor-free `Phi` for the weights `w345` and the caps of `thm:345`. -/
theorem Phi345_eq_PhiFF (c13 c21 c31 r b g : ℤ) :
    (Phi345 r b g : ℚ) = PhiFF w345 (caps345 c13 c21 c31) r b g := by
  simp only [PhiFF, PhiGen, w345, caps345, Phi345, Weights.W, ch2, Weights.cT12, Weights.cT13,
    Weights.cT21, Weights.cT23, Weights.cT31, Weights.cT32, id]
  push_cast; ring

/-- "Fixing the weights": `Phi = 2 + 7178x + 117x² + 6y + 20xy` with
`(r,b,g) = (24-x, 56-y, 74+x+y)`. -/
theorem thm345_identity (x y : ℤ) :
    Phi345 (24 - x) (56 - y) (74 + x + y) = 2 + 7178 * x + 117 * x ^ 2 + 6 * y + 20 * x * y := by
  unfold Phi345; ring

/-- Step (iii) of `thm:345`: `Phi ≥ 2` at every profile with `r + b + g = 154`, `r ≤ 24`,
`b ≤ 56` (no green cap is used). -/
theorem thm345_Phi_ge (r b g : ℤ) (hs : r + b + g = 154) (hr : r ≤ 24) (hb : b ≤ 56) :
    2 ≤ Phi345 r b g := by
  have h := thm345_identity (24 - r) (56 - b)
  rw [show 24 - (24 - r) = r by ring, show 56 - (56 - b) = b by ring,
    show 74 + (24 - r) + (56 - b) = g by omega] at h
  rw [h]
  have hx : 0 ≤ 24 - r := by omega
  have hy : 0 ≤ 56 - b := by omega
  nlinarith [mul_nonneg hx hy, sq_nonneg (24 - r)]

/-- Theorem `thm:345`, step (iii): no nonempty vertex set with colour-degree profiles
`r v + b v + g v = 154`, `r v ≤ 24`, `b v ≤ 56` has `Σ_v Phi(d(v)) ≤ 0` (the floor-free
inequality of Section `sec:types` for these weights and caps); indeed `Σ_v Phi ≥ 2|V|`. -/
theorem thm345_contradiction {V : Type*} [Fintype V] [Nonempty V] (r b g : V → ℕ)
    (hs : ∀ v, r v + b v + g v = 154) (hr : ∀ v, r v ≤ 24) (hb : ∀ v, b v ≤ 56)
    (c13 c21 c31 : ℤ)
    (hsum : ∑ v, PhiFF w345 (caps345 c13 c21 c31) (r v) (b v) (g v) ≤ 0) : False := by
  have : 0 < ∑ v, PhiFF w345 (caps345 c13 c21 c31) (r v) (b v) (g v) := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro v _
    rw [← Phi345_eq_PhiFF]
    have := thm345_Phi_ge (r v) (b v) (g v) (by have := hs v; omega)
      (by have := hr v; omega) (by have := hb v; omega)
    exact_mod_cast (by omega : (0 : ℤ) < Phi345 (r v) (b v) (g v))
  linarith

/-- "The choice of `α` and `γ`": `63/47 ≤ 39/29 < 35/26`, the interval has width `7/1222`, and
no fraction with denominator below `29` lies in it. With the green cap the lower end would be
`Phi(0,2) = 14(3γ-4α) > 0`, giving the interval `4/3 < γ/α < 35/26` of width `1/78`. -/
theorem thm345_choice :
    (63 / 47 : ℚ) ≤ 39 / 29 ∧ (39 / 29 : ℚ) < 35 / 26 ∧ (35 / 26 : ℚ) - 63 / 47 = 7 / 1222 ∧
    (∀ p q : ℕ, 0 < q → q < 29 → ¬ (63 * q ≤ 47 * p ∧ 26 * p < 35 * q)) ∧
    (∀ α γ : ℚ, (70 * α - 52 * γ) + (70 * α + 132 * γ) * 0 + 3 * γ * 0 ^ 2
        + (47 * γ - 63 * α) * 2 + 2 * (γ - α) * 0 * 2 = 14 * (3 * γ - 4 * α)) ∧
    (35 / 26 : ℚ) - 4 / 3 = 1 / 78 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun p q hq hq' => ?_, fun α γ => by ring,
    by norm_num⟩
  interval_cases q <;> omega

/-- "The endpoint `γ/α = 4/3`": for `α = 3`, `γ = 4`, `Phi = 2 + 738x + 12x² - y + 2xy`, which is
`-2` at `(x,y) = (0,4)`, also with the floors (profile `(24, 52, 78)`); under the green cap
`x + y ≤ 2`, `Phi ≥ 0` with equality only at `(0,2)`, the profile `(24, 54, 76)`. -/
theorem thm345_endpoint (c13 c21 c31 : ℤ) :
    (∀ x y : ℤ, PhiFF (wAG 3 4) (caps345 c13 c21 c31) (24 - x) (56 - y) (74 + x + y)
        = 2 + 738 * x + 12 * x ^ 2 - y + 2 * x * y) ∧
    PhiFF (wAG 3 4) (caps345 c13 c21 c31) 24 52 78 = -2 ∧
    PhiFl (wAG 3 4) (caps345 c13 c21 c31) 24 52 78 = -2 ∧
    (∀ x y : ℤ, 0 ≤ x → 0 ≤ y → x + y ≤ 2 →
      0 ≤ (2 + 738 * x + 12 * x ^ 2 - y + 2 * x * y) ∧
      ((2 + 738 * x + 12 * x ^ 2 - y + 2 * x * y) = 0 ↔ x = 0 ∧ y = 2)) := by
  refine ⟨fun x y => ?_, ?_, ?_, fun x y hx hy hxy => ?_⟩
  · rw [thm345_reduction]; ring
  · have := thm345_reduction 3 4 c13 c21 c31 0 4
    norm_num at this ⊢; rw [this]
  · simp only [PhiFl, PhiGen, wAG, caps345, Weights.W, ch2, Weights.cT12, Weights.cT13,
      Weights.cT21, Weights.cT23, Weights.cT31, Weights.cT32]
    norm_num
  · have : x ≤ 2 := by omega
    have : y ≤ 2 := by omega
    interval_cases x <;> interval_cases y <;> norm_num

/-- "A divisibility argument modulo 3" after `thm:345`: the caps `C₃₁ = 17`, `C₃₂ = 29`,
`C₃₃ = 29` sum to `75 = 76 - 1`, so `e₃(N₃(v)) = 76·29/2 = 1102` and
`3M₃ = 155·1102 = 170810`, which is not divisible by `3`. -/
theorem thm345_mod3 :
    17 + 29 + 29 = 76 - 1 ∧ 76 * 29 / 2 = 1102 ∧ 155 * 1102 = 170810 ∧ ¬ (3 ∣ 170810) := by
  decide

/-! ### The weights of `L` (display `eq:L`) -/

/-- The weights `(-2, 4, 4; 1, 1, -2)` of `L`. -/
def wL : Weights := ⟨-2, 4, 4, 1, 1, -2⟩

/-- Requiring the coefficients of `X`, `T₁₂`, `T₁₃`, `T₂₃`, `T₃₂` to vanish forces
`w₁₂ = w₁₃ = -w₁/2`, `w₂₃ = w₁`, `w₂ = w₃ = -2w₁`. -/
theorem wL_forced (w : Weights) (hX : w.cX = 0) (h12 : w.cT12 = 0) (h13 : w.cT13 = 0)
    (h23 : w.cT23 = 0) (h32 : w.cT32 = 0) :
    w.w12 = -w.w1 / 2 ∧ w.w13 = -w.w1 / 2 ∧ w.w23 = w.w1 ∧ w.w2 = -2 * w.w1 ∧
      w.w3 = -2 * w.w1 := by
  simp only [Weights.cX, Weights.cT12, Weights.cT13, Weights.cT23, Weights.cT32] at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Display `eq:L`: `Σ_v L = 6T₂₁ + 6T₃₁ + 12M₂ + 12M₃`, and the sign conditions hold. -/
theorem wL_coeffs :
    wL.cX = 0 ∧ wL.cT12 = 0 ∧ wL.cT13 = 0 ∧ wL.cT21 = 6 ∧ wL.cT23 = 0 ∧ wL.cT31 = 6 ∧
      wL.cT32 = 0 ∧ 3 * wL.w2 = 12 ∧ 3 * wL.w3 = 12 ∧ wL.SignConditions := by
  simp only [Weights.SignConditions, wL, Weights.cX, Weights.cT12, Weights.cT13,
    Weights.cT21, Weights.cT23, Weights.cT31, Weights.cT32]
  norm_num

/-- `L = -2 binom(r,2) + 4 binom(b,2) + 4 binom(g,2) + rb + rg - 2bg`, as an integer
polynomial. -/
def L (r b g : ℤ) : ℤ :=
  -(r * (r - 1)) + 2 * (b * (b - 1)) + 2 * (g * (g - 1)) + r * b + r * g - 2 * b * g

theorem L_eq_W (r b g : ℤ) : (L r b g : ℚ) = wL.W r b g := by
  simp only [L, wL, Weights.W, ch2]; push_cast; ring

/-- The expansion after `eq:L`: for `δ_r + δ_b + δ_g = 0`,
`L(d + δ) = L(d) + ∇L(d)·δ - 6δ_bδ_g`, with `binom(d,2)' = d - 1/2`. Subtracting a linear
function, the same holds for every floor-free `Phi` below. -/
theorem L_expansion (r b g x y z : ℚ) (h : x + y + z = 0) :
    wL.W (r + x) (b + y) (g + z) = wL.W r b g + (-2 * (r - 1 / 2) + b + g) * x
      + (4 * (b - 1 / 2) + r - 2 * g) * y + (4 * (g - 1 / 2) + r - 2 * b) * z - 6 * y * z := by
  have hx : x = -y - z := by linarith
  subst hx
  simp only [wL, Weights.W, ch2]; ring

/-! ### Theorem `thm:346`: `R(3,4,6) ≤ 276`

Ramsey inputs: `r ≤ D₁ ≤ 40` from the published `R(4,6) ≤ 41`, `b ≤ D₂ ≤ 87` from
`R(3,3,6) ≤ 88` (Theorem `thm:336`), and the caps `C₂₁ = R(3,6) - 1 = 17`, `C₂₂ = 17`,
`C₃₁ = R(4,5) - 1 = 24`, `C₃₃ ≤ 76` from `R(3,4,4) ≤ 77`. No green cap. -/

/-- The caps of `thm:346`; `c12`, `c13`, `c23`, `c32` multiply vanishing coefficients. -/
def caps346 (c12 c13 c23 c32 : ℤ) : Caps := ⟨c12, c13, 17, c23, 24, c32, 17, 76⟩

/-- `Phi = L - 85b - 224g`. -/
def Phi346 (r b g : ℤ) : ℤ := L r b g - 85 * b - 224 * g

theorem Phi346_eq_PhiFF (c12 c13 c23 c32 r b g : ℤ) :
    (Phi346 r b g : ℚ) = PhiFF wL (caps346 c12 c13 c23 c32) r b g := by
  simp only [PhiFF, PhiGen, wL, caps346, Phi346, L, Weights.W, ch2, Weights.cT12,
    Weights.cT13, Weights.cT21, Weights.cT23, Weights.cT31, Weights.cT32, id]
  push_cast; ring

/-- At `(40, 87, 148)`: `L = 40564`, `85b + 224g = 40547`, `Phi = 17`, `∇Phi = (156, 5, 232)`. -/
theorem thm346_values :
    L 40 87 148 = 40564 ∧ 85 * 87 + 224 * 148 = 40547 ∧ Phi346 40 87 148 = 17 ∧
    (-2 * (40 - 1 / 2) + 87 + 148 : ℚ) = 156 ∧ (4 * (87 - 1 / 2) + 40 - 2 * 148 - 85 : ℚ) = 5 ∧
    (4 * (148 - 1 / 2) + 40 - 2 * 87 - 224 : ℚ) = 232 := by
  refine ⟨by decide, by decide, by decide, by norm_num, by norm_num, by norm_num⟩

/-- "Reduction to two variables": with `(r,b,g) = (40-x, 87-y, 148+x+y)`,
`Phi = 17 + 76x + 227y + 6xy + 6y²`. -/
theorem thm346_identity (x y : ℤ) :
    Phi346 (40 - x) (87 - y) (148 + x + y) = 17 + 76 * x + 227 * y + 6 * x * y + 6 * y ^ 2 := by
  unfold Phi346 L; ring

/-- Step (iii) of `thm:346`: `Phi ≥ 17` at every profile with `r + b + g = 275`, `r ≤ 40`,
`b ≤ 87`. -/
theorem thm346_Phi_ge (r b g : ℤ) (hs : r + b + g = 275) (hr : r ≤ 40) (hb : b ≤ 87) :
    17 ≤ Phi346 r b g := by
  have h := thm346_identity (40 - r) (87 - b)
  rw [show 40 - (40 - r) = r by ring, show 87 - (87 - b) = b by ring,
    show 148 + (40 - r) + (87 - b) = g by omega] at h
  rw [h]
  have hx : 0 ≤ 40 - r := by omega
  have hy : 0 ≤ 87 - b := by omega
  nlinarith [mul_nonneg hx hy, sq_nonneg (87 - b)]

/-- Theorem `thm:346`, step (iii): no nonempty vertex set with profiles `r v + b v + g v = 275`,
`r v ≤ 40`, `b v ≤ 87` has `Σ_v Phi(d(v)) ≤ 0` (floor-free `Phi` for the weights of `L` and the
caps of `thm:346`). -/
theorem thm346_contradiction {V : Type*} [Fintype V] [Nonempty V] (r b g : V → ℕ)
    (hs : ∀ v, r v + b v + g v = 275) (hr : ∀ v, r v ≤ 40) (hb : ∀ v, b v ≤ 87)
    (c12 c13 c23 c32 : ℤ)
    (hsum : ∑ v, PhiFF wL (caps346 c12 c13 c23 c32) (r v) (b v) (g v) ≤ 0) : False := by
  have : 0 < ∑ v, PhiFF wL (caps346 c12 c13 c23 c32) (r v) (b v) (g v) := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro v _
    rw [← Phi346_eq_PhiFF]
    have := thm346_Phi_ge (r v) (b v) (g v) (by have := hs v; omega)
      (by have := hr v; omega) (by have := hb v; omega)
    exact_mod_cast (by omega : (0 : ℤ) < Phi346 (r v) (b v) (g v))
  linarith

/-- "Why it stops here" after `thm:346`: with `x ≥ 1` the minimum rises to `17 + 76 = 93`, but
at `n = 275` the profile `(39, 87, 148)` gives `Phi = -140`, and `-135` with the floors. -/
theorem thm346_stop (c12 c13 c23 c32 : ℤ) :
    17 + 76 = 93 ∧ Phi346 39 87 148 = -140 ∧
    PhiFl wL (caps346 c12 c13 c23 c32) 39 87 148 = -135 := by
  refine ⟨by norm_num, by decide, ?_⟩
  simp only [PhiFl, PhiGen, wL, caps346, Weights.W, ch2, Weights.cT12, Weights.cT13,
    Weights.cT21, Weights.cT23, Weights.cT31, Weights.cT32]
  norm_num

/-! ### Theorem `thm:355`: `R(3,5,5) ≤ 346`

Ramsey inputs: `r ≤ 45` from `R(5,5) ≤ 46`, `b, g ≤ 154` from `R(3,4,5) ≤ 155`
(Theorem `thm:345`), and the caps `C₂₁ = C₃₁ = R(4,5) - 1 = 24`, `C₂₂ = C₃₃ ≤ 56` from
`R(3,3,5) ≤ 57`. -/

/-- The caps of `thm:355`; `c12`, `c13`, `c23`, `c32` multiply vanishing coefficients. -/
def caps355 (c12 c13 c23 c32 : ℤ) : Caps := ⟨c12, c13, 24, c23, 24, c32, 56, 56⟩

/-- `Phi = L - 184(b + g)`. -/
def Phi355 (r b g : ℤ) : ℤ := L r b g - 184 * (b + g)

theorem Phi355_eq_PhiFF (c12 c13 c23 c32 r b g : ℤ) :
    (Phi355 r b g : ℚ) = PhiFF wL (caps355 c12 c13 c23 c32) r b g := by
  simp only [PhiFF, PhiGen, wL, caps355, Phi355, L, Weights.W, ch2, Weights.cT12,
    Weights.cT13, Weights.cT21, Weights.cT23, Weights.cT31, Weights.cT32, id]
  push_cast; ring

/-- At `(37, 154, 154)`: `L = 56880 = 184(b+g) + 208`, and `∇Phi = (235, 159, 159)`. -/
theorem thm355_values :
    L 37 154 154 = 56880 ∧ 56880 = 184 * (154 + 154) + 208 ∧ Phi355 37 154 154 = 208 ∧
    (-2 * (37 - 1 / 2) + 154 + 154 : ℚ) = 235 ∧
    (4 * (154 - 1 / 2) + 37 - 2 * 154 - 184 : ℚ) = 159 := by
  refine ⟨by decide, by decide, by decide, by norm_num, by norm_num⟩

/-- "Reduction to two variables": with `(r,b,g) = (37+x+y, 154-x, 154-y)`,
`Phi = 208 + 76x + 76y - 6xy`. -/
theorem thm355_identity (x y : ℤ) :
    Phi355 (37 + x + y) (154 - x) (154 - y) = 208 + 76 * x + 76 * y - 6 * x * y := by
  unfold Phi355 L; ring

/-- Step (iii) of `thm:355`: `Phi ≥ 208` at every profile with `r + b + g = 345`, `r ≤ 45`,
`b ≤ 154`, `g ≤ 154` (here `x + y ≤ 8` is needed, for the term `-6xy`). -/
theorem thm355_Phi_ge (r b g : ℤ) (hs : r + b + g = 345) (hr : r ≤ 45) (hb : b ≤ 154)
    (hg : g ≤ 154) : 208 ≤ Phi355 r b g := by
  have h := thm355_identity (154 - b) (154 - g)
  rw [show 37 + (154 - b) + (154 - g) = r by omega, show 154 - (154 - b) = b by ring,
    show 154 - (154 - g) = g by ring] at h
  rw [h]
  have hx : 0 ≤ 154 - b := by omega
  have hy : 0 ≤ 154 - g := by omega
  have hy8 : 0 ≤ 76 - 6 * (154 - g) := by omega
  nlinarith [mul_nonneg hx hy8]

/-- Theorem `thm:355`, step (iii): no nonempty vertex set with profiles `r v + b v + g v = 345`,
`r v ≤ 45`, `b v ≤ 154`, `g v ≤ 154` has `Σ_v Phi(d(v)) ≤ 0`. -/
theorem thm355_contradiction {V : Type*} [Fintype V] [Nonempty V] (r b g : V → ℕ)
    (hs : ∀ v, r v + b v + g v = 345) (hr : ∀ v, r v ≤ 45) (hb : ∀ v, b v ≤ 154)
    (hg : ∀ v, g v ≤ 154) (c12 c13 c23 c32 : ℤ)
    (hsum : ∑ v, PhiFF wL (caps355 c12 c13 c23 c32) (r v) (b v) (g v) ≤ 0) : False := by
  have : 0 < ∑ v, PhiFF wL (caps355 c12 c13 c23 c32) (r v) (b v) (g v) := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro v _
    rw [← Phi355_eq_PhiFF]
    have := thm355_Phi_ge (r v) (b v) (g v) (by have := hs v; omega)
      (by have := hr v; omega) (by have := hb v; omega) (by have := hg v; omega)
    exact_mod_cast (by omega : (0 : ℤ) < Phi355 (r v) (b v) (g v))
  linarith

/-- "Why it stops here" after `thm:355`: at `n = 345` the profile `(36, 154, 154)` gives
`Phi = -28`, with or without the floors. -/
theorem thm355_stop (c12 c13 c23 c32 : ℤ) :
    Phi355 36 154 154 = -28 ∧ PhiFl wL (caps355 c12 c13 c23 c32) 36 154 154 = -28 := by
  refine ⟨by decide, ?_⟩
  simp only [PhiFl, PhiGen, wL, caps355, Weights.W, ch2, Weights.cT12, Weights.cT13,
    Weights.cT21, Weights.cT23, Weights.cT31, Weights.cT32]
  norm_num

/-! ### Proposition `prop:supp`: `R(3,4,7) ≤ 456`, `R(3,4,8) ≤ 700`, `R(3,5,6) ≤ 683`, and
`458`, `705`, `685` without the starred inputs

Admissible profiles are `(r, b, g) ∈ ℕ³` with `r + b + g = n - 1`, `r ≤ D₁`, `b ≤ D₂`,
`g ≤ D₃`. The margins (least values of `Phi` with the floors) are checked by exhaustive kernel
evaluation over the whole box `r ≤ D₁`, `b ≤ D₂`; the paper's hand reductions are checked as
polynomial identities and floor-free lower bounds.

Ramsey inputs (caps), as in the table of the proof:
* `(3,4,7)`, `n = 456`: `D = (57*, 128, 275)` from `R(4,7) ≤ 58*`, `R(3,3,7) ≤ 129`,
  `R(3,4,6) ≤ 276`; `(C, C₃₃) = (22, 154)` from `R(3,7) = 23`, `R(3,4,5) ≤ 155`.
  Unstarred, `n = 458`: `D₁ = 60` from `R(4,7) ≤ 61`.
* `(3,4,8)`, `n = 700`: `D = (78*, 178, 455*)` from `R(4,8) ≤ 79*`, `R(3,3,8) ≤ 179`,
  `R(3,4,7) ≤ 456`; `(C, C₃₃) = (27, 275)` from `R(3,8) = 28`, `R(3,4,6) ≤ 276`.
  Unstarred, `n = 705`: `D = (83, 178, 457)` from `R(4,8) ≤ 84`, `R(3,4,7) ≤ 458`.
* `(3,5,6)`, `n = 683`: `D = (84*, 275, 345)` from `R(5,6) ≤ 85*`, `R(3,4,6) ≤ 276`,
  `R(3,5,5) ≤ 346`; `(C₂₁, C₂₂, C₃₁, C₃₃) = (39*, 87, 45, 154)` from `R(4,6) ≤ 40*`,
  `R(3,3,6) ≤ 88`, `R(5,5) ≤ 46`, `R(3,4,5) ≤ 155`.
  Unstarred, `n = 685`: `D₁ = 86` from `R(5,6) ≤ 87`, `C₂₁ = 40` from `R(4,6) ≤ 41`. -/

/-- The weights `(2, 2, 2; 2, -1, -1)` used for `(3,4,k)`. -/
def wS : Weights := ⟨2, 2, 2, 2, -1, -1⟩

/-- `Σ_v W = 6T₁₂ + 6T₂₁ + 6M₂ + 6M₃`, and the sign conditions hold. -/
theorem wS_coeffs :
    wS.cX = 0 ∧ wS.cT12 = 6 ∧ wS.cT13 = 0 ∧ wS.cT21 = 6 ∧ wS.cT23 = 0 ∧ wS.cT31 = 0 ∧
      wS.cT32 = 0 ∧ 3 * wS.w2 = 6 ∧ 3 * wS.w3 = 6 ∧ wS.SignConditions := by
  simp only [Weights.SignConditions, wS, Weights.cX, Weights.cT12, Weights.cT13,
    Weights.cT21, Weights.cT23, Weights.cT31, Weights.cT32]
  norm_num

/-- `W = 2binom(r,2) + 2binom(b,2) + 2binom(g,2) + 2rb - rg - bg` as an integer polynomial. -/
def WS (r b g : ℤ) : ℤ := r * (r - 1) + b * (b - 1) + g * (g - 1) + 2 * r * b - r * g - b * g

theorem WS_eq_W (r b g : ℤ) : (WS r b g : ℚ) = wS.W r b g := by
  simp only [WS, wS, Weights.W, ch2]; push_cast; ring

/-- "The margins by hand": `W = s(s-1) + g(g-1) - gs` with `s = r + b`, and
`3Cr + 4Cb = 3Cs + CD₂ - C(D₂ - b)`. -/
theorem WS_s_form (r b g C D2 : ℤ) :
    WS r b g = (r + b) * (r + b - 1) + g * (g - 1) - g * (r + b) ∧
      3 * C * r + 4 * C * b = 3 * C * (r + b) + C * D2 - C * (D2 - b) := by
  constructor
  · unfold WS; ring
  · ring

/-- The caps for `(3,4,k)`: `C₁₂ = C₂₁ = C₂₂ = C` and `C₃₃`; the others multiply vanishing
coefficients. -/
def capsS (C C33 c13 c23 c31 c32 : ℤ) : Caps := ⟨C, c13, C, c23, c31, c32, C, C33⟩

/-- `Phi = W - 6⌊Cr/2⌋ - 8⌊Cb/2⌋ - 2⌊C₃₃g/2⌋`, for `(3,4,k)`. -/
def PhiS (C C33 r b g : ℤ) : ℤ := WS r b g - 6 * (C * r / 2) - 8 * (C * b / 2) - 2 * (C33 * g / 2)

/-- `PhiS` is the paper's `Phi` with the floors, for the weights `wS` and the caps `capsS`. -/
theorem PhiS_eq_PhiFl (C C33 c13 c23 c31 c32 r b g : ℤ) :
    (PhiS C C33 r b g : ℚ) = PhiFl wS (capsS C C33 c13 c23 c31 c32) r b g := by
  simp only [PhiFl, PhiGen, capsS, floor_half]
  rw [← WS_eq_W]
  simp only [PhiS, wS, Weights.cT12, Weights.cT13, Weights.cT21, Weights.cT23, Weights.cT31,
    Weights.cT32]
  push_cast; ring

/-- The caps for `(3,5,6)` with the weights of `L`: `C₂₁`, `C₂₂`, `C₃₁`, `C₃₃`; the others
multiply vanishing coefficients. -/
def caps356 (c21 c22 c31 c33 c12 c13 c23 c32 : ℤ) : Caps := ⟨c12, c13, c21, c23, c31, c32, c22, c33⟩

/-- `Phi = L - 6⌊C₂₁b/2⌋ - 4⌊C₂₂b/2⌋ - 6⌊C₃₁g/2⌋ - 4⌊C₃₃g/2⌋`, for `(3,5,6)`. -/
def PhiL (c21 c22 c31 c33 r b g : ℤ) : ℤ :=
  L r b g - 6 * (c21 * b / 2) - 4 * (c22 * b / 2) - 6 * (c31 * g / 2) - 4 * (c33 * g / 2)

theorem PhiL_eq_PhiFl (c21 c22 c31 c33 c12 c13 c23 c32 r b g : ℤ) :
    (PhiL c21 c22 c31 c33 r b g : ℚ) =
      PhiFl wL (caps356 c21 c22 c31 c33 c12 c13 c23 c32) r b g := by
  simp only [PhiFl, PhiGen, caps356, floor_half]
  rw [← L_eq_W]
  simp only [PhiL, wL, Weights.cT12, Weights.cT13, Weights.cT21, Weights.cT23, Weights.cT31,
    Weights.cT32]
  push_cast; ring

/-- The admissible profiles `(r, b, g)` with `r + b + g = S` (`S = n - 1`), `r ≤ D₁`, `b ≤ D₂`,
`g ≤ D₃`, enumerated by `(r, b)`. -/
def profiles (S D1 D2 D3 : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (((Finset.range (D1 + 1)) ×ˢ (Finset.range (D2 + 1))).filter
      (fun p => p.1 + p.2 ≤ S ∧ S - (p.1 + p.2) ≤ D3)).map
    ⟨fun p => (p.1, p.2, S - (p.1 + p.2)), fun p q h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.1⟩

theorem mem_profiles (S D1 D2 D3 r b g : ℕ) :
    (r, b, g) ∈ profiles S D1 D2 D3 ↔ r + b + g = S ∧ r ≤ D1 ∧ b ≤ D2 ∧ g ≤ D3 := by
  simp only [profiles, Finset.mem_map, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Function.Embedding.coeFn_mk, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a, c, ⟨⟨ha, hc⟩, h1, h2⟩, rfl, rfl, rfl⟩; omega
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨r, b, ⟨⟨by omega, by omega⟩, by omega, by omega⟩, rfl, rfl,
      by omega⟩

/-- Reduction of a margin claim over all admissible profiles to a decidable statement over the
box `r ≤ D₁`, `b ≤ D₂`. -/
theorem margin_of_box (S D1 D2 D3 : ℕ) (P : ℕ → ℕ → ℕ → Prop)
    (hbox : ∀ r, r < D1 + 1 → ∀ b, b < D2 + 1 → r + b ≤ S → S - (r + b) ≤ D3 →
      P r b (S - (r + b)))
    (r b g : ℕ) (hs : r + b + g = S) (hr : r ≤ D1) (hb : b ≤ D2) (hg : g ≤ D3) : P r b g := by
  have := hbox r (by omega) b (by omega) (by omega) (by omega)
  rwa [show S - (r + b) = g by omega] at this

/-! #### `(3,4,7)`, `n = 456` -/

theorem supp347_box : ∀ r : ℕ, r < 57 + 1 → ∀ b : ℕ, b < 128 + 1 → r + b ≤ 455 →
    455 - (r + b) ≤ 275 →
    114 ≤ PhiS 22 154 (r : ℤ) (b : ℤ) ((455 - (r + b) : ℕ) : ℤ) := by
  decide +kernel

/-- `R(3,4,7) ≤ 456`: `21` admissible profiles, margin `114`, attained at `(57, 128, 270)`. -/
theorem prop_supp_347 :
    (profiles 455 57 128 275).card = 21 ∧
    (∀ r b g : ℕ, r + b + g = 455 → r ≤ 57 → b ≤ 128 → g ≤ 275 → 114 ≤ PhiS 22 154 r b g) ∧
    PhiS 22 154 57 128 270 = 114 := by
  refine ⟨by rw [profiles, Finset.card_map]; decide +kernel, ?_, by decide⟩
  intro r b g hs hr hb hg
  exact margin_of_box 455 57 128 275 (fun r b g => 114 ≤ PhiS 22 154 r b g) supp347_box
    r b g hs hr hb hg

/-- The hand reduction for `(3,4,7)`, `n = 456`: as `C = 22` and `C₃₃ = 154` are even the floors
have no effect, `Phi = 3s² - 1277s + 133684 + 22(128 - b)` with `s = r + b`, `g = 455 - s`, and
on `s ≤ 185` this is at least `114`. -/
theorem supp347_hand (r b : ℤ) :
    PhiS 22 154 r b (455 - (r + b)) =
        3 * (r + b) ^ 2 - 1277 * (r + b) + 133684 + 22 * (128 - b) ∧
      (r + b ≤ 185 → b ≤ 128 → 114 ≤ 3 * (r + b) ^ 2 - 1277 * (r + b) + 133684 + 22 * (128 - b)) := by
  constructor
  · unfold PhiS WS
    rw [show 22 * r / 2 = 11 * r by omega, show 22 * b / 2 = 11 * b by omega,
      show 154 * (455 - (r + b)) / 2 = 77 * (455 - (r + b)) by omega]
    ring
  · intro hs hb
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ 185 - (r + b)) (by omega : (0 : ℤ) ≤ 722 - 3 * (r + b) + 3 * 0)]

/-! #### `(3,4,8)`, `n = 700` -/

theorem supp348_box : ∀ r : ℕ, r < 78 + 1 → ∀ b : ℕ, b < 178 + 1 → r + b ≤ 699 →
    699 - (r + b) ≤ 455 →
    312 ≤ PhiS 27 275 (r : ℤ) (b : ℤ) ((699 - (r + b) : ℕ) : ℤ) := by
  decide +kernel

/-- `R(3,4,8) ≤ 700`: `91` admissible profiles, margin `312`, attained at `(78, 178, 443)`. -/
theorem prop_supp_348 :
    (profiles 699 78 178 455).card = 91 ∧
    (∀ r b g : ℕ, r + b + g = 699 → r ≤ 78 → b ≤ 178 → g ≤ 455 → 312 ≤ PhiS 27 275 r b g) ∧
    PhiS 27 275 78 178 443 = 312 := by
  refine ⟨by rw [profiles, Finset.card_map]; decide +kernel, ?_, by decide⟩
  intro r b g hs hr hb hg
  exact margin_of_box 699 78 178 455 (fun r b g => 312 ≤ PhiS 27 275 r b g) supp348_box
    r b g hs hr hb hg

/-- The hand reduction for `(3,4,8)`, `n = 700`: the floor-free `Phi` is
`3s² - 1903s + 290871 + 27(178 - b)` with `g = 699 - s`, at least `311` on `s ≤ 256`; at
`(78, 178, 443)` the floors add `1`. -/
theorem supp348_hand (r b : ℤ) :
    WS r b (699 - (r + b)) - 81 * r - 108 * b - 275 * (699 - (r + b)) =
        3 * (r + b) ^ 2 - 1903 * (r + b) + 290871 + 27 * (178 - b) ∧
      (r + b ≤ 256 → b ≤ 178 → 311 ≤ 3 * (r + b) ^ 2 - 1903 * (r + b) + 290871 + 27 * (178 - b)) ∧
      WS 78 178 443 - 81 * 78 - 108 * 178 - 275 * 443 = 311 := by
  refine ⟨by unfold WS; ring, fun hs hb => ?_, by decide⟩
  nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ 256 - (r + b)) (by omega : (0 : ℤ) ≤ 1135 - 3 * (r + b))]

/-! #### `(3,5,6)`, `n = 683` -/

theorem supp356_box : ∀ r : ℕ, r < 84 + 1 → ∀ b : ℕ, b < 275 + 1 → r + b ≤ 682 →
    682 - (r + b) ≤ 345 →
    116 ≤ PhiL 39 87 45 154 (r : ℤ) (b : ℤ) ((682 - (r + b) : ℕ) : ℤ) := by
  decide +kernel

/-- `R(3,5,6) ≤ 683`: `276` admissible profiles, margin `116`, attained at `(62, 275, 345)`. -/
theorem prop_supp_356 :
    (profiles 682 84 275 345).card = 276 ∧
    (∀ r b g : ℕ, r + b + g = 682 → r ≤ 84 → b ≤ 275 → g ≤ 345 →
      116 ≤ PhiL 39 87 45 154 r b g) ∧
    PhiL 39 87 45 154 62 275 345 = 116 := by
  refine ⟨by rw [profiles, Finset.card_map]; decide +kernel, ?_, by decide⟩
  intro r b g hs hr hb hg
  exact margin_of_box 682 84 275 345 (fun r b g => 116 ≤ PhiL 39 87 45 154 r b g) supp356_box
    r b g hs hr hb hg

/-- The hand reduction for `(3,5,6)`, `n = 683`: the floor-free `Phi` is `L - 291b - 443g`, and
with `(r,b,g) = (62+x+y, 275-x, 345-y)` it is `108 + 318x + 50y - 6xy`, at least `108` when
`x, y ≥ 0` and `x + y ≤ 22`; at `(62, 275, 345)` the floors add `3 + 2 + 3`. -/
theorem supp356_hand (x y : ℤ) :
    L (62 + x + y) (275 - x) (345 - y) - 291 * (275 - x) - 443 * (345 - y) =
        108 + 318 * x + 50 * y - 6 * x * y ∧
      (0 ≤ x → 0 ≤ y → x + y ≤ 22 → 108 ≤ 108 + 318 * x + 50 * y - 6 * x * y) ∧
      (6 * (39 * 275 / 2) + 3 = 6 * 39 * 275 / 2 ∧ 4 * (87 * 275 / 2) + 2 = 4 * 87 * 275 / 2 ∧
        6 * (45 * 345 / 2) + 3 = 6 * 45 * 345 / 2 ∧ 4 * (154 * 345 / 2) = 4 * 154 * 345 / 2) := by
  refine ⟨by unfold L; ring, fun hx hy hxy => ?_, by decide⟩
  nlinarith [mul_nonneg hx (by omega : (0 : ℤ) ≤ 318 - 6 * y)]

/-! #### Without the starred inputs: `(3,4,7)`, `n = 458` -/

theorem supp347u_box : ∀ r : ℕ, r < 60 + 1 → ∀ b : ℕ, b < 128 + 1 → r + b ≤ 457 →
    457 - (r + b) ≤ 275 →
    26 ≤ PhiS 22 154 (r : ℤ) (b : ℤ) ((457 - (r + b) : ℕ) : ℤ) := by
  decide +kernel

/-- `R(3,4,7) ≤ 458` without starred inputs: margin `26`, attained at `(60, 128, 269)`
(`28` admissible profiles; the paper does not state this count). -/
theorem prop_supp_347_unstarred :
    (profiles 457 60 128 275).card = 28 ∧
    (∀ r b g : ℕ, r + b + g = 457 → r ≤ 60 → b ≤ 128 → g ≤ 275 → 26 ≤ PhiS 22 154 r b g) ∧
    PhiS 22 154 60 128 269 = 26 := by
  refine ⟨by rw [profiles, Finset.card_map]; decide +kernel, ?_, by decide⟩
  intro r b g hs hr hb hg
  exact margin_of_box 457 60 128 275 (fun r b g => 26 ≤ PhiS 22 154 r b g) supp347u_box
    r b g hs hr hb hg

/-- The hand reduction for `(3,4,7)`, `n = 458`: `Phi = 3s² - 1283s + 135198 + 22(128 - b)`
with `g = 457 - s`, at least `26` on `s ≤ 188`. -/
theorem supp347u_hand (r b : ℤ) :
    PhiS 22 154 r b (457 - (r + b)) =
        3 * (r + b) ^ 2 - 1283 * (r + b) + 135198 + 22 * (128 - b) ∧
      (r + b ≤ 188 → b ≤ 128 → 26 ≤ 3 * (r + b) ^ 2 - 1283 * (r + b) + 135198 + 22 * (128 - b)) := by
  constructor
  · unfold PhiS WS
    rw [show 22 * r / 2 = 11 * r by omega, show 22 * b / 2 = 11 * b by omega,
      show 154 * (457 - (r + b)) / 2 = 77 * (457 - (r + b)) by omega]
    ring
  · intro hs hb
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ 188 - (r + b)) (by omega : (0 : ℤ) ≤ 719 - 3 * (r + b))]

/-! #### Without the starred inputs: `(3,4,8)`, `n = 705` -/

theorem supp348u_box : ∀ r : ℕ, r < 83 + 1 → ∀ b : ℕ, b < 178 + 1 → r + b ≤ 704 →
    704 - (r + b) ≤ 457 →
    275 ≤ PhiS 27 275 (r : ℤ) (b : ℤ) ((704 - (r + b) : ℕ) : ℤ) := by
  decide +kernel

/-- `R(3,4,8) ≤ 705` without starred inputs: margin `275`, attained at `(83, 178, 443)`
(`120` admissible profiles; the paper does not state this count). -/
theorem prop_supp_348_unstarred :
    (profiles 704 83 178 457).card = 120 ∧
    (∀ r b g : ℕ, r + b + g = 704 → r ≤ 83 → b ≤ 178 → g ≤ 457 → 275 ≤ PhiS 27 275 r b g) ∧
    PhiS 27 275 83 178 443 = 275 := by
  refine ⟨by rw [profiles, Finset.card_map]; decide +kernel, ?_, by decide⟩
  intro r b g hs hr hb hg
  exact margin_of_box 704 83 178 457 (fun r b g => 275 ≤ PhiS 27 275 r b g) supp348u_box
    r b g hs hr hb hg

/-- The hand reduction for `(3,4,8)`, `n = 705`: the floor-free `Phi` is
`3s² - 1918s + 296506 + 27(178 - b)` with `g = 704 - s`; at least `271` on `s ≤ 261`, `271` at
`(83, 178, 443)`, and `626` at `(82, 178, 444)`. -/
theorem supp348u_hand (r b : ℤ) :
    WS r b (704 - (r + b)) - 81 * r - 108 * b - 275 * (704 - (r + b)) =
        3 * (r + b) ^ 2 - 1918 * (r + b) + 296506 + 27 * (178 - b) ∧
      (r + b ≤ 261 → b ≤ 178 → 271 ≤ 3 * (r + b) ^ 2 - 1918 * (r + b) + 296506 + 27 * (178 - b)) ∧
      WS 83 178 443 - 81 * 83 - 108 * 178 - 275 * 443 = 271 ∧
      WS 82 178 444 - 81 * 82 - 108 * 178 - 275 * 444 = 626 := by
  refine ⟨by unfold WS; ring, fun hs hb => ?_, by decide, by decide⟩
  nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ 261 - (r + b)) (by omega : (0 : ℤ) ≤ 1135 - 3 * (r + b))]

/-! #### Without the starred inputs: `(3,5,6)`, `n = 685` -/

theorem supp356u_box : ∀ r : ℕ, r < 86 + 1 → ∀ b : ℕ, b < 275 + 1 → r + b ≤ 684 →
    684 - (r + b) ≤ 345 →
    278 ≤ PhiL 40 87 45 154 (r : ℤ) (b : ℤ) ((684 - (r + b) : ℕ) : ℤ) := by
  decide +kernel

/-- `R(3,5,6) ≤ 685` without starred inputs: margin `278`, attained at `(64, 275, 345)`
(`276` admissible profiles; the paper does not state this count). -/
theorem prop_supp_356_unstarred :
    (profiles 684 86 275 345).card = 276 ∧
    (∀ r b g : ℕ, r + b + g = 684 → r ≤ 86 → b ≤ 275 → g ≤ 345 →
      278 ≤ PhiL 40 87 45 154 r b g) ∧
    PhiL 40 87 45 154 64 275 345 = 278 := by
  refine ⟨by rw [profiles, Finset.card_map]; decide +kernel, ?_, by decide⟩
  intro r b g hs hr hb hg
  exact margin_of_box 684 86 275 345 (fun r b g => 278 ≤ PhiL 40 87 45 154 r b g) supp356u_box
    r b g hs hr hb hg

/-- The hand reduction for `(3,5,6)`, `n = 685`: the floor-free `Phi` is `L - 294b - 443g`, and
with `(r,b,g) = (64+x+y, 275-x, 345-y)` it is `273 + 315x + 44y - 6xy`, at least `273` when
`x, y ≥ 0` and `x + y ≤ 22`. -/
theorem supp356u_hand (x y : ℤ) :
    L (64 + x + y) (275 - x) (345 - y) - 294 * (275 - x) - 443 * (345 - y) =
        273 + 315 * x + 44 * y - 6 * x * y ∧
      (0 ≤ x → 0 ≤ y → x + y ≤ 22 → 273 ≤ 273 + 315 * x + 44 * y - 6 * x * y) := by
  refine ⟨by unfold L; ring, fun hx hy hxy => ?_⟩
  nlinarith [mul_nonneg hx (by omega : (0 : ℤ) ≤ 315 - 6 * y)]

/-- Proposition `prop:supp`, step (iii), in contradiction form for `(3,4,7)`, `n = 456`: no
nonempty vertex set with admissible profiles has `Σ_v Phi(d(v)) ≤ 0`, where `Phi` is the paper's
`Phi` with the floors for the weights `(2,2,2;2,-1,-1)` and caps `C = 22`, `C₃₃ = 154`. -/
theorem prop_supp_347_contradiction {V : Type*} [Fintype V] [Nonempty V] (r b g : V → ℕ)
    (hs : ∀ v, r v + b v + g v = 455) (hr : ∀ v, r v ≤ 57) (hb : ∀ v, b v ≤ 128)
    (hg : ∀ v, g v ≤ 275) (c13 c23 c31 c32 : ℤ)
    (hsum : ∑ v, PhiFl wS (capsS 22 154 c13 c23 c31 c32) (r v) (b v) (g v) ≤ 0) : False := by
  have : 0 < ∑ v, PhiFl wS (capsS 22 154 c13 c23 c31 c32) (r v) (b v) (g v) := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro v _
    rw [← PhiS_eq_PhiFl]
    have := prop_supp_347.2.1 (r v) (b v) (g v) (hs v) (hr v) (hb v) (hg v)
    exact_mod_cast (by omega : (0 : ℤ) < PhiS 22 154 (r v) (b v) (g v))
  linarith

/-- The same for `(3,4,8)`, `n = 700`, caps `C = 27`, `C₃₃ = 275`. -/
theorem prop_supp_348_contradiction {V : Type*} [Fintype V] [Nonempty V] (r b g : V → ℕ)
    (hs : ∀ v, r v + b v + g v = 699) (hr : ∀ v, r v ≤ 78) (hb : ∀ v, b v ≤ 178)
    (hg : ∀ v, g v ≤ 455) (c13 c23 c31 c32 : ℤ)
    (hsum : ∑ v, PhiFl wS (capsS 27 275 c13 c23 c31 c32) (r v) (b v) (g v) ≤ 0) : False := by
  have : 0 < ∑ v, PhiFl wS (capsS 27 275 c13 c23 c31 c32) (r v) (b v) (g v) := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro v _
    rw [← PhiS_eq_PhiFl]
    have := prop_supp_348.2.1 (r v) (b v) (g v) (hs v) (hr v) (hb v) (hg v)
    exact_mod_cast (by omega : (0 : ℤ) < PhiS 27 275 (r v) (b v) (g v))
  linarith

/-- The same for `(3,5,6)`, `n = 683`, with the weights of `L` and caps
`(C₂₁, C₂₂, C₃₁, C₃₃) = (39, 87, 45, 154)`. -/
theorem prop_supp_356_contradiction {V : Type*} [Fintype V] [Nonempty V] (r b g : V → ℕ)
    (hs : ∀ v, r v + b v + g v = 682) (hr : ∀ v, r v ≤ 84) (hb : ∀ v, b v ≤ 275)
    (hg : ∀ v, g v ≤ 345) (c12 c13 c23 c32 : ℤ)
    (hsum : ∑ v, PhiFl wL (caps356 39 87 45 154 c12 c13 c23 c32) (r v) (b v) (g v) ≤ 0) :
    False := by
  have : 0 < ∑ v, PhiFl wL (caps356 39 87 45 154 c12 c13 c23 c32) (r v) (b v) (g v) := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro v _
    rw [← PhiL_eq_PhiFl]
    have := prop_supp_356.2.1 (r v) (b v) (g v) (hs v) (hr v) (hb v) (hg v)
    exact_mod_cast (by omega : (0 : ℤ) < PhiL 39 87 45 154 (r v) (b v) (g v))
  linarith

/-- The contradiction form without the starred inputs, `(3,4,7)`, `n = 458`. -/
theorem prop_supp_347_unstarred_contradiction {V : Type*} [Fintype V] [Nonempty V]
    (r b g : V → ℕ) (hs : ∀ v, r v + b v + g v = 457) (hr : ∀ v, r v ≤ 60)
    (hb : ∀ v, b v ≤ 128) (hg : ∀ v, g v ≤ 275) (c13 c23 c31 c32 : ℤ)
    (hsum : ∑ v, PhiFl wS (capsS 22 154 c13 c23 c31 c32) (r v) (b v) (g v) ≤ 0) : False := by
  have : 0 < ∑ v, PhiFl wS (capsS 22 154 c13 c23 c31 c32) (r v) (b v) (g v) := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro v _
    rw [← PhiS_eq_PhiFl]
    have := prop_supp_347_unstarred.2.1 (r v) (b v) (g v) (hs v) (hr v) (hb v) (hg v)
    exact_mod_cast (by omega : (0 : ℤ) < PhiS 22 154 (r v) (b v) (g v))
  linarith

/-- The contradiction form without the starred inputs, `(3,4,8)`, `n = 705`. -/
theorem prop_supp_348_unstarred_contradiction {V : Type*} [Fintype V] [Nonempty V]
    (r b g : V → ℕ) (hs : ∀ v, r v + b v + g v = 704) (hr : ∀ v, r v ≤ 83)
    (hb : ∀ v, b v ≤ 178) (hg : ∀ v, g v ≤ 457) (c13 c23 c31 c32 : ℤ)
    (hsum : ∑ v, PhiFl wS (capsS 27 275 c13 c23 c31 c32) (r v) (b v) (g v) ≤ 0) : False := by
  have : 0 < ∑ v, PhiFl wS (capsS 27 275 c13 c23 c31 c32) (r v) (b v) (g v) := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro v _
    rw [← PhiS_eq_PhiFl]
    have := prop_supp_348_unstarred.2.1 (r v) (b v) (g v) (hs v) (hr v) (hb v) (hg v)
    exact_mod_cast (by omega : (0 : ℤ) < PhiS 27 275 (r v) (b v) (g v))
  linarith

/-- The contradiction form without the starred inputs, `(3,5,6)`, `n = 685`, caps
`(C₂₁, C₂₂, C₃₁, C₃₃) = (40, 87, 45, 154)`. -/
theorem prop_supp_356_unstarred_contradiction {V : Type*} [Fintype V] [Nonempty V]
    (r b g : V → ℕ) (hs : ∀ v, r v + b v + g v = 684) (hr : ∀ v, r v ≤ 86)
    (hb : ∀ v, b v ≤ 275) (hg : ∀ v, g v ≤ 345) (c12 c13 c23 c32 : ℤ)
    (hsum : ∑ v, PhiFl wL (caps356 40 87 45 154 c12 c13 c23 c32) (r v) (b v) (g v) ≤ 0) :
    False := by
  have : 0 < ∑ v, PhiFl wL (caps356 40 87 45 154 c12 c13 c23 c32) (r v) (b v) (g v) := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro v _
    rw [← PhiL_eq_PhiFl]
    have := prop_supp_356_unstarred.2.1 (r v) (b v) (g v) (hs v) (hr v) (hb v) (hg v)
    exact_mod_cast (by omega : (0 : ℤ) < PhiL 40 87 45 154 (r v) (b v) (g v))
  linarith

/-! ## Theorem `thm:444a`: `R(4,4,4) ≤ 226`

Ramsey inputs, through Lemmas `lem:caps` and `lem:fivecaps` (taken here as the hypotheses
`hA … hE` and the profile caps): every colour degree is at most `76` (from `R(3,4,4) ≤ 77`),
`|N_i(v) ∩ N_i(u)| ≤ 17` (from `R(2,4,4) = R(4,4) = 18`), and `|N_i(v) ∩ N_j(u)| ≤ 29` for
`j ≠ i` (from `R(3,3,4) = 30`). The identities (I), (II), (III) of Lemma `lem:444id` and the star
densities of Lemma `lem:stars` are also hypotheses. -/

/-- Steps 1 to 3 of `thm:444a`: the identities (I), (II), (III) of Lemma `lem:444id` and the five
caps of Lemma `lem:fivecaps` at `n' = 223` give display `eq:star226`,
`15692·3s + 2189·6t ≤ 2189`. (The proof combines the caps with multipliers `1/2`, `38/45`,
`7/45`, `1`, `1`; the terms in `m` cancel, so no sign condition on `m` is needed.) -/
theorem thm444a_star226 (s t m b A B' C D E : ℚ)
    (hI : 9 * m + 18 * b = 1 + 6 * s - 6 * t)
    (hII : 3 * A + 6 * B' + 6 * D + 6 * E = 2 * s + m) (hIII : B' = C)
    (hA : A ≤ 74 / 223 * m) (hB : B' ≤ 29 / 223 * m) (hC : C ≤ 17 / 223 * b)
    (hD : D ≤ 29 / 223 * b) (hE : E ≤ 17 / 223 * b) :
    15692 * (3 * s) + 2189 * (6 * t) ≤ 2189 := by
  linarith

/-- Step 1 of `thm:444a` for every `0 ≤ λ ≤ 1`:
`(2s + m)/6 ≤ ((37 + 29λ)m + (63 - 17λ)b)/n'` with `n' = 223`. -/
theorem thm444a_step1 (s m b A B' C D E lam : ℚ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hII : 3 * A + 6 * B' + 6 * D + 6 * E = 2 * s + m) (hIII : B' = C)
    (hA : A ≤ 74 / 223 * m) (hB : B' ≤ 29 / 223 * m) (hC : C ≤ 17 / 223 * b)
    (hD : D ≤ 29 / 223 * b) (hE : E ≤ 17 / 223 * b) :
    (2 * s + m) / 6 ≤ ((37 + 29 * lam) * m + (63 - 17 * lam) * b) / 223 := by
  nlinarith [mul_le_mul_of_nonneg_left hB h0, mul_le_mul_of_nonneg_left hC (by linarith : 0 ≤ 1 - lam)]

/-- The arithmetic of Steps 2 and 3 of `thm:444a`: after substituting (I) the coefficient of `m`
is `(11 + 75λ)/(2n')`, which equals `1/6` for `λ = (n' - 33)/225`; then
`63 - 17λ = (14736 - 17n')/225`; at `n' = 223`, `λ = 38/45`, `14736 - 17·223 = 10945`,
`1350·223 = 5·60210`, `10945 = 5·2189`, and `60210 - 6·2189 = 3·15692`. -/
theorem thm444a_arith (n' : ℚ) (hn : n' ≠ 0) :
    (37 + 29 * ((n' - 33) / 225) - (63 - 17 * ((n' - 33) / 225)) / 2) / n' =
        (11 + 75 * ((n' - 33) / 225)) / (2 * n') ∧
      (11 + 75 * ((n' - 33) / 225)) / (2 * n') = 1 / 6 ∧
      63 - 17 * ((n' - 33) / 225) = (14736 - 17 * n') / 225 ∧
      ((223 : ℚ) - 33) / 225 = 38 / 45 ∧ (14736 : ℤ) - 17 * 223 = 10945 ∧
      (1350 : ℤ) * 223 = 5 * 60210 ∧ (10945 : ℤ) = 5 * 2189 ∧ (60210 : ℤ) - 6 * 2189 = 3 * 15692 := by
  refine ⟨?_, ?_, by ring, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · field_simp; ring
  · field_simp; ring

/-- The falling factorial `(x)₃ = x(x-1)(x-2)`. -/
def ff3 (x : ℤ) : ℤ := x * (x - 1) * (x - 2)

/-- The numerator `15692 Σ_i (d_i)₃ + 6·2189 d₁d₂d₃ - 2189 (n-1)₃` of `Phi` in Step 4 of
`thm:444a`, with `n = 226`. -/
def num444a (d1 d2 d3 : ℤ) : ℤ :=
  15692 * (ff3 d1 + ff3 d2 + ff3 d3) + 6 * 2189 * (d1 * d2 * d3) - 2189 * ff3 225

/-- `Phi(d) = num/(n-1)₃` of Step 4 of `thm:444a`. -/
def Phi444a (d1 d2 d3 : ℤ) : ℚ := (num444a d1 d2 d3 : ℚ) / (ff3 225 : ℚ)

/-- `(n-1)₃ = 225·224·223 = 11239200` and `2189 (n-1)₃ = 24602608800`. -/
theorem thm444a_consts : ff3 225 = 225 * 224 * 223 ∧ ff3 225 = 11239200 ∧
    2189 * ff3 225 = 24602608800 := by decide

/-- `Phi` is symmetric in the `d_i`. -/
theorem num444a_symm (d1 d2 d3 : ℤ) :
    num444a d1 d2 d3 = num444a d2 d1 d3 ∧ num444a d1 d2 d3 = num444a d1 d3 d2 := by
  constructor <;> (unfold num444a; ring)

set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Step 4 of `thm:444a`: every profile with entries at most `76` summing to `225` is, up to
order, one of `(73,76,76)`, `(74,75,76)` and `(75,75,75)` (each of which is such a profile). -/
theorem thm444a_profiles : ∀ d1 : ℕ, d1 < 77 → ∀ d2 : ℕ, d2 < 77 → d1 + d2 ≤ 225 → 225 - (d1 + d2) ≤ 76 →
    (d1, d2, 225 - (d1 + d2)) ∈
      ([(73, 76, 76), (76, 73, 76), (76, 76, 73), (74, 75, 76), (74, 76, 75), (75, 74, 76),
        (75, 76, 74), (76, 74, 75), (76, 75, 74), (75, 75, 75)] : List (ℕ × ℕ × ℕ)) := by
  decide +kernel

/-- The table of Step 5 of `thm:444a`: `Σ_i (d_i)₃`, `d₁d₂d₃`, the numerator and `Phi`. -/
theorem thm444a_table :
    (ff3 73 + ff3 76 + ff3 76 = 1216776 ∧ 73 * 76 * 76 = 421648 ∧
      num444a 73 76 76 = 28965024 ∧ Phi444a 73 76 76 = 451 / 175) ∧
    (ff3 74 + ff3 75 + ff3 76 = 1215894 ∧ 74 * 75 * 76 = 421800 ∧
      num444a 74 75 76 = 17121048 ∧ Phi444a 74 75 76 = 457 / 300) ∧
    (ff3 75 + ff3 75 + ff3 75 = 1215450 ∧ 75 * 75 * 75 = 421875 ∧
      num444a 75 75 75 = 11138850 ∧ Phi444a 75 75 75 = 111 / 112) := by
  have hN : ((ff3 225 : ℤ) : ℚ) = 11239200 := by rw [show ff3 225 = 11239200 by decide]; norm_num
  refine ⟨⟨by decide, by norm_num, by decide, ?_⟩, ⟨by decide, by norm_num, by decide, ?_⟩,
    ⟨by decide, by norm_num, by decide, ?_⟩⟩ <;> simp only [Phi444a, hN]
  · rw [show num444a 73 76 76 = 28965024 by decide]; norm_num
  · rw [show num444a 74 75 76 = 17121048 by decide]; norm_num
  · rw [show num444a 75 75 75 = 11138850 by decide]; norm_num

theorem thm444a_box : ∀ d1 : ℕ, d1 < 77 → ∀ d2 : ℕ, d2 < 77 → d1 + d2 ≤ 225 →
    225 - (d1 + d2) ≤ 76 → 0 < num444a (d1 : ℤ) (d2 : ℤ) ((225 - (d1 + d2) : ℕ) : ℤ) := by
  decide +kernel

/-- Step 5 of `thm:444a`: `Phi > 0` at every profile with entries at most `76` summing to `225`. -/
theorem thm444a_Phi_pos (d1 d2 d3 : ℕ) (hs : d1 + d2 + d3 = 225) (h1 : d1 ≤ 76) (h2 : d2 ≤ 76)
    (h3 : d3 ≤ 76) : 0 < Phi444a d1 d2 d3 := by
  have := thm444a_box d1 (by omega) d2 (by omega) (by omega) (by omega)
  rw [show 225 - (d1 + d2) = d3 by omega] at this
  unfold Phi444a
  apply div_pos (by exact_mod_cast this)
  rw [show ff3 225 = 11239200 by decide]; norm_num

/-- Steps 4 and 5 of `thm:444a`: with `s` and `t` given by Lemma `lem:stars` for `n = 226`,
the left side of `eq:star226` minus `2189` is the average of `Phi(d(v))` over the vertices. -/
theorem thm444a_average {V : Type*} [Fintype V] (hV : Fintype.card V = 226)
    (d1 d2 d3 : V → ℕ) (s t : ℚ)
    (hs : s = (∑ v, ((ff3 (d1 v) + ff3 (d2 v) + ff3 (d3 v) : ℤ) : ℚ)) / (3 * 226 * ff3 225))
    (ht : t = (∑ v, ((d1 v * d2 v * d3 v : ℕ) : ℚ)) / (226 * ff3 225)) :
    15692 * (3 * s) + 2189 * (6 * t) - 2189 = (∑ v, Phi444a (d1 v) (d2 v) (d3 v)) / 226 := by
  subst hs ht
  have hN : ((ff3 225 : ℤ) : ℚ) = 11239200 := by rw [show ff3 225 = 11239200 by decide]; norm_num
  simp only [Phi444a, num444a, ← Finset.sum_div]
  push_cast
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, hV, nsmul_eq_mul]
  rw [hN]
  push_cast
  ring

/-- Theorem `thm:444a`, numerical skeleton: there are no `226` vertices with colour-degree
profiles `d(v)` (entries at most `76`, summing to `225`) and numbers `s, t, m, b, A, B', C, D, E`
such that `s`, `t` are the star densities of Lemma `lem:stars`, the identities (I), (II), (III)
of Lemma `lem:444id` hold, and the five caps of Lemma `lem:fivecaps` hold at `n' = 223`. -/
theorem thm444a_contradiction {V : Type*} [Fintype V] (hV : Fintype.card V = 226)
    (d1 d2 d3 : V → ℕ) (hsum : ∀ v, d1 v + d2 v + d3 v = 225)
    (hcap : ∀ v, d1 v ≤ 76 ∧ d2 v ≤ 76 ∧ d3 v ≤ 76) (s t m b A B' C D E : ℚ)
    (hs : s = (∑ v, ((ff3 (d1 v) + ff3 (d2 v) + ff3 (d3 v) : ℤ) : ℚ)) / (3 * 226 * ff3 225))
    (ht : t = (∑ v, ((d1 v * d2 v * d3 v : ℕ) : ℚ)) / (226 * ff3 225))
    (hI : 9 * m + 18 * b = 1 + 6 * s - 6 * t)
    (hII : 3 * A + 6 * B' + 6 * D + 6 * E = 2 * s + m) (hIII : B' = C)
    (hA : A ≤ 74 / 223 * m) (hB : B' ≤ 29 / 223 * m) (hC : C ≤ 17 / 223 * b)
    (hD : D ≤ 29 / 223 * b) (hE : E ≤ 17 / 223 * b) : False := by
  have hstar := thm444a_star226 s t m b A B' C D E hI hII hIII hA hB hC hD hE
  have havg := thm444a_average hV d1 d2 d3 s t hs ht
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hpos : 0 < ∑ v, Phi444a (d1 v) (d2 v) (d3 v) :=
    Finset.sum_pos (fun v _ => thm444a_Phi_pos (d1 v) (d2 v) (d3 v) (hsum v) (hcap v).1
      (hcap v).2.1 (hcap v).2.2) Finset.univ_nonempty
  have : 0 < (∑ v, Phi444a (d1 v) (d2 v) (d3 v)) / 226 := by positivity
  linarith

/-- "Why it stops here" after `thm:444a`: at `n = 225` (`n' = 222`, `λ = 21/25`) the star
inequality is `1444·3s + 203·6t ≤ 203`, the profiles are, up to order, `(72,76,76)`,
`(73,75,76)`, `(74,74,76)`, `(74,75,75)`, and the corresponding `Phi` is negative at every
profile, with the values `-1369/1561`, `-1597/1561`, `-239/223`, `-28009/24976`. -/
def num444a225 (d1 d2 d3 : ℤ) : ℤ :=
  1444 * (ff3 d1 + ff3 d2 + ff3 d3) + 6 * 203 * (d1 * d2 * d3) - 203 * ff3 224

theorem thm444a_stop_arith :
    ((222 : ℚ) - 33) / 225 = 21 / 25 ∧ (1350 : ℤ) * 222 = 54 * 5550 ∧
      (14736 : ℤ) - 17 * 222 = 54 * 203 ∧ (5550 : ℤ) - 6 * 203 = 3 * 1444 := by
  norm_num

set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem thm444a_stop_box : ∀ d1 : ℕ, d1 < 77 → ∀ d2 : ℕ, d2 < 77 → d1 + d2 ≤ 224 →
    224 - (d1 + d2) ≤ 76 → num444a225 (d1 : ℤ) (d2 : ℤ) ((224 - (d1 + d2) : ℕ) : ℤ) < 0 ∧
      (d1, d2, 224 - (d1 + d2)) ∈
        ([(72, 76, 76), (76, 72, 76), (76, 76, 72), (73, 75, 76), (73, 76, 75), (75, 73, 76),
          (75, 76, 73), (76, 73, 75), (76, 75, 73), (74, 74, 76), (74, 76, 74), (76, 74, 74),
          (74, 75, 75), (75, 74, 75), (75, 75, 74)] : List (ℕ × ℕ × ℕ)) := by
  decide +kernel

theorem thm444a_stop_values :
    (num444a225 72 76 76 : ℚ) / (ff3 224 : ℚ) = -1369 / 1561 ∧
    (num444a225 73 75 76 : ℚ) / (ff3 224 : ℚ) = -1597 / 1561 ∧
    (num444a225 74 74 76 : ℚ) / (ff3 224 : ℚ) = -239 / 223 ∧
    (num444a225 74 75 75 : ℚ) / (ff3 224 : ℚ) = -28009 / 24976 := by
  simp only [num444a225, ff3]; norm_num

end FiniteChecks
end RamseyLean

#print axioms RamseyLean.FiniteChecks.line_a
#print axioms RamseyLean.FiniteChecks.line_a_ceil
#print axioms RamseyLean.FiniteChecks.line_b
#print axioms RamseyLean.FiniteChecks.density_collect
#print axioms RamseyLean.FiniteChecks.pk_values
#print axioms RamseyLean.FiniteChecks.thm336_F_eq
#print axioms RamseyLean.FiniteChecks.admissible_of_caps
#print axioms RamseyLean.FiniteChecks.thm337_contradiction_caps
#print axioms RamseyLean.FiniteChecks.lem_m7_124_caps
#print axioms RamseyLean.FiniteChecks.thm338_contradiction_caps
#print axioms RamseyLean.FiniteChecks.thm336_F_shift
#print axioms RamseyLean.FiniteChecks.thm336_F_pos
#print axioms RamseyLean.FiniteChecks.thm336_contradiction
#print axioms RamseyLean.FiniteChecks.thm336_stop
#print axioms RamseyLean.FiniteChecks.commonnbr_collect
#print axioms RamseyLean.FiniteChecks.pk_nonneg
#print axioms RamseyLean.FiniteChecks.chord_identity
#print axioms RamseyLean.FiniteChecks.chord_le
#print axioms RamseyLean.FiniteChecks.m6_table_beta_alpha
#print axioms RamseyLean.FiniteChecks.m6_beta_pos
#print axioms RamseyLean.FiniteChecks.m6_q_floor_root
#print axioms RamseyLean.FiniteChecks.m6_root_rounding
#print axioms RamseyLean.FiniteChecks.m6_disc
#print axioms RamseyLean.FiniteChecks.m6_ceil
#print axioms RamseyLean.FiniteChecks.m6_ceil_int
#print axioms RamseyLean.FiniteChecks.lem_m6more
#print axioms RamseyLean.FiniteChecks.thm337_admissible
#print axioms RamseyLean.FiniteChecks.thm337_Psi_eq
#print axioms RamseyLean.FiniteChecks.thm337_table
#print axioms RamseyLean.FiniteChecks.thm337_Psi_pos
#print axioms RamseyLean.FiniteChecks.thm337_contradiction
#print axioms RamseyLean.FiniteChecks.thm337_comparison
#print axioms RamseyLean.FiniteChecks.m7_admissible
#print axioms RamseyLean.FiniteChecks.m7_table
#print axioms RamseyLean.FiniteChecks.m7_chord
#print axioms RamseyLean.FiniteChecks.m7_round
#print axioms RamseyLean.FiniteChecks.lem_m7_124
#print axioms RamseyLean.FiniteChecks.m7_step
#print axioms RamseyLean.FiniteChecks.thm338_admissible
#print axioms RamseyLean.FiniteChecks.thm338_table
#print axioms RamseyLean.FiniteChecks.thm338_Psi_pos
#print axioms RamseyLean.FiniteChecks.thm338_contradiction
#print axioms RamseyLean.FiniteChecks.PhiFF_le_PhiFl
#print axioms RamseyLean.FiniteChecks.floor_half
#print axioms RamseyLean.FiniteChecks.wAG_coeffs
#print axioms RamseyLean.FiniteChecks.wAG_sign_iff
#print axioms RamseyLean.FiniteChecks.thm345_PhiFF_general
#print axioms RamseyLean.FiniteChecks.thm345_reduction
#print axioms RamseyLean.FiniteChecks.w345_eq
#print axioms RamseyLean.FiniteChecks.w345_coeffs
#print axioms RamseyLean.FiniteChecks.Phi345_eq_PhiFF
#print axioms RamseyLean.FiniteChecks.thm345_identity
#print axioms RamseyLean.FiniteChecks.thm345_Phi_ge
#print axioms RamseyLean.FiniteChecks.thm345_contradiction
#print axioms RamseyLean.FiniteChecks.thm345_choice
#print axioms RamseyLean.FiniteChecks.thm345_endpoint
#print axioms RamseyLean.FiniteChecks.thm345_mod3
#print axioms RamseyLean.FiniteChecks.wL_forced
#print axioms RamseyLean.FiniteChecks.wL_coeffs
#print axioms RamseyLean.FiniteChecks.L_eq_W
#print axioms RamseyLean.FiniteChecks.L_expansion
#print axioms RamseyLean.FiniteChecks.Phi346_eq_PhiFF
#print axioms RamseyLean.FiniteChecks.thm346_values
#print axioms RamseyLean.FiniteChecks.thm346_identity
#print axioms RamseyLean.FiniteChecks.thm346_Phi_ge
#print axioms RamseyLean.FiniteChecks.thm346_contradiction
#print axioms RamseyLean.FiniteChecks.thm346_stop
#print axioms RamseyLean.FiniteChecks.Phi355_eq_PhiFF
#print axioms RamseyLean.FiniteChecks.thm355_values
#print axioms RamseyLean.FiniteChecks.thm355_identity
#print axioms RamseyLean.FiniteChecks.thm355_Phi_ge
#print axioms RamseyLean.FiniteChecks.thm355_contradiction
#print axioms RamseyLean.FiniteChecks.thm355_stop
#print axioms RamseyLean.FiniteChecks.wS_coeffs
#print axioms RamseyLean.FiniteChecks.WS_s_form
#print axioms RamseyLean.FiniteChecks.PhiS_eq_PhiFl
#print axioms RamseyLean.FiniteChecks.PhiL_eq_PhiFl
#print axioms RamseyLean.FiniteChecks.mem_profiles
#print axioms RamseyLean.FiniteChecks.prop_supp_347
#print axioms RamseyLean.FiniteChecks.supp347_hand
#print axioms RamseyLean.FiniteChecks.prop_supp_348
#print axioms RamseyLean.FiniteChecks.supp348_hand
#print axioms RamseyLean.FiniteChecks.prop_supp_356
#print axioms RamseyLean.FiniteChecks.supp356_hand
#print axioms RamseyLean.FiniteChecks.prop_supp_347_unstarred
#print axioms RamseyLean.FiniteChecks.supp347u_hand
#print axioms RamseyLean.FiniteChecks.prop_supp_348_unstarred
#print axioms RamseyLean.FiniteChecks.supp348u_hand
#print axioms RamseyLean.FiniteChecks.prop_supp_356_unstarred
#print axioms RamseyLean.FiniteChecks.supp356u_hand
#print axioms RamseyLean.FiniteChecks.prop_supp_347_contradiction
#print axioms RamseyLean.FiniteChecks.prop_supp_348_contradiction
#print axioms RamseyLean.FiniteChecks.prop_supp_356_contradiction
#print axioms RamseyLean.FiniteChecks.prop_supp_347_unstarred_contradiction
#print axioms RamseyLean.FiniteChecks.prop_supp_348_unstarred_contradiction
#print axioms RamseyLean.FiniteChecks.prop_supp_356_unstarred_contradiction
#print axioms RamseyLean.FiniteChecks.thm444a_star226
#print axioms RamseyLean.FiniteChecks.thm444a_step1
#print axioms RamseyLean.FiniteChecks.thm444a_arith
#print axioms RamseyLean.FiniteChecks.thm444a_consts
#print axioms RamseyLean.FiniteChecks.num444a_symm
#print axioms RamseyLean.FiniteChecks.thm444a_profiles
#print axioms RamseyLean.FiniteChecks.thm444a_table
#print axioms RamseyLean.FiniteChecks.thm444a_Phi_pos
#print axioms RamseyLean.FiniteChecks.thm444a_average
#print axioms RamseyLean.FiniteChecks.thm444a_contradiction
#print axioms RamseyLean.FiniteChecks.thm444a_stop_arith
#print axioms RamseyLean.FiniteChecks.thm444a_stop_box
#print axioms RamseyLean.FiniteChecks.thm444a_stop_values
