import RamseyLean.LocalCombinatorics
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# `R(3,3,6) ≤ 88` (Theorem `thm:336` of the paper)

Formalisation of the proof of Theorem `thm:336` of `paper/neighbourhood_counting.tex`,
together with the general-`k` lemmas it uses.

* Conventional notions: `IsMonoClique`, `NoMonoK` ("no colour-`a` `K_m` inside `S`"),
  `AvoidsOn c s₁ s₂ s₃ S` ("the colouring is `(s₁,s₂,s₃)`-avoiding on `S`"), and the usual
  Ramsey statements `RamseyLE s₁ s₂ s₃ B` (`R(s₁,s₂,s₃) ≤ B`) and `RamseyLE2 s t B`
  (`R(s,t) ≤ B`). Ramsey numbers enter only through caps of the form
  "every vertex set on which `c` is `s`-avoiding has at most `B - 1` vertices", and
  `card_lt_of_ramseyLE` derives such a cap from `RamseyLE`.
* Lemma `lem:caps` (the parts used): `red_degree_le`, `blue_degree_le`,
  `avoidsOn_common_green`, and the green cap inside `degree_admissible`.
* The merged red-or-blue graph `H = mergedGraph c _ _` (a `SimpleGraph`), its triangles
  `H.cliqueFinset 3`, and the apex count `triangles_eq_sum_edgesInside`
  (`T(H) = Σ_v (e_2(N_1(v)) + e_1(N_2(v)))`).
* Lemma `lem:apex`: `apex_bound` (`T(H) ≤ Σ_v A_k(h_v)` and `2 Σ_v A_k(h_v) ≤ (k-1) Σ_v h_v`).
* Lemma `lem:commonnbr`: `commonnbr` (without the bracket) and `commonnbr_bracket`
  (with `p_k`).
* Lemma `lem:line`(b): `line_b`.
* Theorem `thm:336`: `r336` (any symmetric colouring of a vertex set of size 88, under the
  three caps) and `ramseyLE_336_88` (`R(3,6) ≤ 18` and `R(3,3,4) ≤ 30` give
  `R(3,3,6) ≤ 88`).

Internally a colouring is a symmetric map `c : V → V → Colour` with green diagonal (then the
red and blue neighbourhoods of `RamseyLocal` exclude the vertex itself); `r336` removes the
diagonal assumption via `diagGreen`.
-/

set_option linter.unusedSectionVars false

namespace RamseyLean.R336

open RamseyLocal Colour Finset

section Conventional

variable {V : Type*}

/-- `T` is a clique of colour `a`: every pair of distinct vertices of `T` has colour `a`. -/
def IsMonoClique (c : V → V → Colour) (a : Colour) (T : Finset V) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → c x y = a

/-- `S` contains no colour-`a` `K_m`: no `m`-element subset of `S` is a colour-`a` clique. -/
def NoMonoK (c : V → V → Colour) (a : Colour) (m : ℕ) (S : Finset V) : Prop :=
  ¬ ∃ T ⊆ S, T.card = m ∧ IsMonoClique c a T

/-- The colouring is `(s₁,s₂,s₃)`-avoiding on the vertex set `S`:
no red `K_{s₁}`, no blue `K_{s₂}` and no green `K_{s₃}` inside `S`. -/
def AvoidsOn (c : V → V → Colour) (s₁ s₂ s₃ : ℕ) (S : Finset V) : Prop :=
  NoMonoK c red s₁ S ∧ NoMonoK c blue s₂ S ∧ NoMonoK c green s₃ S

/-- The conventional statement `R(s₁,s₂,s₃) ≤ B`: every 3-colouring of the edges of `K_B`
(a symmetric map on `Fin B`; the diagonal plays no role) contains, for some colour `i`,
a colour-`i` clique on `s_i` vertices. -/
def RamseyLE (s₁ s₂ s₃ B : ℕ) : Prop :=
  ∀ c : Fin B → Fin B → Colour, (∀ x y, c x y = c y x) → ¬ AvoidsOn c s₁ s₂ s₃ Finset.univ

/-- The conventional two-colour statement `R(s,t) ≤ B`: every red/blue colouring
(`true`/`false`) of the edges of `K_B` has a `true` `K_s` or a `false` `K_t`. -/
def RamseyLE2 (s t B : ℕ) : Prop :=
  ∀ d : Fin B → Fin B → Bool, (∀ x y, d x y = d y x) →
    (∃ T : Finset (Fin B), T.card = s ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → d x y = true) ∨
    (∃ T : Finset (Fin B), T.card = t ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → d x y = false)

theorem IsMonoClique.subset {c : V → V → Colour} {a : Colour} {T T' : Finset V}
    (h : IsMonoClique c a T) (hs : T' ⊆ T) : IsMonoClique c a T' :=
  fun x hx y hy hxy => h x (hs hx) y (hs hy) hxy

/-- "No `K_m`" is the same as "every clique has fewer than `m` vertices". -/
theorem noMonoK_iff {c : V → V → Colour} {a : Colour} {m : ℕ} {S : Finset V} :
    NoMonoK c a m S ↔ ∀ T ⊆ S, IsMonoClique c a T → T.card < m := by
  constructor
  · intro h T hT hcl
    by_contra hn
    obtain ⟨T', hT', hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
    exact h ⟨T', hT'.trans hT, hcard, hcl.subset hT'⟩
  · rintro h ⟨T, hT, hcard, hcl⟩
    have := h T hT hcl
    omega

theorem NoMonoK.mono {c : V → V → Colour} {a : Colour} {m : ℕ} {S S' : Finset V}
    (h : NoMonoK c a m S) (hs : S' ⊆ S) : NoMonoK c a m S' :=
  fun ⟨T, hT, hcard, hcl⟩ => h ⟨T, hT.trans hs, hcard, hcl⟩

/-- **Bridge lemma.** The conventional bound `R(s) ≤ B` gives the vertex-set cap used by the
paper: every vertex set on which a colouring is `s`-avoiding has fewer than `B` vertices. -/
theorem card_lt_of_ramseyLE {s₁ s₂ s₃ B : ℕ} (hR : RamseyLE s₁ s₂ s₃ B)
    (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x) (S : Finset V)
    (hS : AvoidsOn c s₁ s₂ s₃ S) : S.card < B := by
  classical
  by_contra hn
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  have hcardT : Fintype.card T = B := by simpa using hTcard
  let e : T ≃ Fin B := Fintype.equivFinOfCardEq hcardT
  let f : Fin B → V := fun i => (e.symm i : V)
  have hf : Function.Injective f := fun i j hij => e.symm.injective (Subtype.ext hij)
  let c' : Fin B → Fin B → Colour := fun i j => c (f i) (f j)
  apply hR c' (fun i j => hsymm _ _)
  have key : ∀ (a : Colour) (m : ℕ), NoMonoK c a m S → NoMonoK c' a m univ := by
    rintro a m hno ⟨T', -, hcard, hcl⟩
    apply hno
    refine ⟨T'.map ⟨f, hf⟩, ?_, by simp [hcard], ?_⟩
    · intro x hx
      simp only [mem_map, Function.Embedding.coeFn_mk] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact hTS (e.symm i).2
    · intro x hx y hy hxy
      simp only [mem_map, Function.Embedding.coeFn_mk] at hx hy
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨j, hj, rfl⟩ := hy
      exact hcl i hi j hj (fun h => hxy (h ▸ rfl))
  exact ⟨key _ _ hS.1, key _ _ hS.2.1, key _ _ hS.2.2⟩

/-- Interchanging red and blue. -/
def swapRB : Colour → Colour
  | red => blue
  | blue => red
  | green => green

theorem isMonoClique_swapRB {c : V → V → Colour} {a : Colour} {T : Finset V} :
    IsMonoClique (fun x y => swapRB (c x y)) a T ↔ IsMonoClique c (swapRB a) T := by
  have h : ∀ b : Colour, swapRB b = a ↔ b = swapRB a := by
    intro b; cases a <;> cases b <;> simp [swapRB]
  simp only [IsMonoClique, h]

/-- `R(s₁,s₂,s₃)` is symmetric in its first two entries. -/
theorem ramseyLE_swap {s₁ s₂ s₃ B : ℕ} (h : RamseyLE s₁ s₂ s₃ B) : RamseyLE s₂ s₁ s₃ B := by
  intro c hsymm hav
  apply h (fun x y => swapRB (c x y)) (fun x y => by simp only; rw [hsymm])
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨T, hT, hcard, hcl⟩
    exact hav.2.1 ⟨T, hT, hcard, isMonoClique_swapRB.mp hcl⟩
  · rintro ⟨T, hT, hcard, hcl⟩
    exact hav.1 ⟨T, hT, hcard, isMonoClique_swapRB.mp hcl⟩
  · rintro ⟨T, hT, hcard, hcl⟩
    exact hav.2.2 ⟨T, hT, hcard, isMonoClique_swapRB.mp hcl⟩

/-- A two-colour bound `R(s,t) ≤ B` is the three-colour bound `R(2,s,t) ≤ B`:
a colouring with no red edge uses only blue and green. -/
theorem ramseyLE_of_ramseyLE2 {s t B : ℕ} (h : RamseyLE2 s t B) : RamseyLE 2 s t B := by
  intro c hsymm hav
  have hnored : ∀ x y : Fin B, x ≠ y → c x y ≠ red := by
    intro x y hxy hr
    apply hav.1
    refine ⟨{x, y}, subset_univ _, card_pair hxy, ?_⟩
    intro u hu w hw huw
    simp only [mem_insert, mem_singleton] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact absurd rfl huw
    · exact hr
    · rw [hsymm]; exact hr
    · exact absurd rfl huw
  rcases h (fun x y => decide (c x y = blue)) (fun x y => by simp only; rw [hsymm]) with
    ⟨T, hcard, hT⟩ | ⟨T, hcard, hT⟩
  · apply hav.2.1
    refine ⟨T, subset_univ _, hcard, fun x hx y hy hxy => ?_⟩
    simpa using hT x hx y hy hxy
  · apply hav.2.2
    refine ⟨T, subset_univ _, hcard, fun x hx y hy hxy => ?_⟩
    have h1 : c x y ≠ blue := by simpa using hT x hx y hy hxy
    have h2 := hnored x y hxy
    cases hc : c x y <;> simp_all

end Conventional

section Internal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Colourings with a green diagonal

Internally we work with a symmetric colouring whose diagonal is green. Then the red and blue
neighbourhoods `neighbourhood c red v`, `neighbourhood c blue v` of `RamseyLocal` do not contain
`v`, and the red-or-blue relation is a simple graph. -/

/-- The red-or-blue graph `H` of a colouring (symmetric, green diagonal). -/
def mergedGraph (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green) : SimpleGraph V where
  Adj x y := c x y ≠ green
  symm := fun x y (h : c x y ≠ green) => (show c y x ≠ green by rwa [hsymm])
  loopless := fun v h => h (hdiag v)

instance mergedGraph.decRel (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green) : DecidableRel (mergedGraph c hsymm hdiag).Adj :=
  fun x y => inferInstanceAs (Decidable (c x y ≠ green))

theorem isH_eq (a : Colour) : isH a = if a = green then 0 else 1 := by
  cases a <;> rfl

theorem isH_mul_self (a : Colour) : isH a * isH a = isH a := by
  cases a <;> rfl

/-- The `H`-degree `h_v`, as a sum of indicators. -/
def hdeg (c : V → V → Colour) (v : V) : ℕ := ∑ w, isH (c v w)

/-- Indicator of an ordered green pair of distinct vertices. -/
def gI (c : V → V → Colour) (x y : V) : ℕ := if x ≠ y ∧ c x y = green then 1 else 0

/-- The green degree `z_v`. -/
def zdeg (c : V → V → Colour) (v : V) : ℕ := ∑ w, gI c v w

/-- The green neighbourhood `N_3(v)` (excluding `v`). -/
def greenNbhd (c : V → V → Colour) (v : V) : Finset V :=
  univ.filter fun w => w ≠ v ∧ c v w = green

theorem mem_greenNbhd {c : V → V → Colour} {v w : V} :
    w ∈ greenNbhd c v ↔ w ≠ v ∧ c v w = green := by
  simp [greenNbhd]

theorem mergedGraph_degree (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green) (v : V) :
    (mergedGraph c hsymm hdiag).degree v = hdeg c v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    card_filter]
  refine sum_congr rfl fun w _ => ?_
  rw [isH_eq]
  by_cases h : c v w = green <;> simp [mergedGraph, h]

/-- `h_v = d_1(v) + d_2(v)`. -/
theorem hdeg_eq_red_add_blue (c : V → V → Colour) (v : V) :
    hdeg c v = (neighbourhood c red v).card + (neighbourhood c blue v).card := by
  have hcard : ∀ a, (neighbourhood c a v).card = ∑ w, colourIndicator c a v w := by
    intro a
    unfold neighbourhood colourIndicator
    rw [card_filter]
  rw [hcard, hcard, ← sum_add_distrib]
  refine sum_congr rfl fun w _ => ?_
  cases h : c v w <;> simp [colourIndicator, isH, h]

/-- Every ordered pair is equal, an `H`-edge, or a green edge, exactly one of them. -/
theorem pair_partition (c : V → V → Colour) (hdiag : ∀ v, c v v = green) (x y : V) :
    (if x = y then 1 else 0) + isH (c x y) + gI c x y = 1 := by
  by_cases hxy : x = y
  · subst hxy; simp [hdiag, isH, gI]
  · cases h : c x y <;> simp [hxy, h, isH, gI]

/-- `1 + h_v + z_v = n`. -/
theorem one_add_hdeg_add_zdeg (c : V → V → Colour) (hdiag : ∀ v, c v v = green) (v : V) :
    1 + hdeg c v + zdeg c v = Fintype.card V := by
  have h := sum_congr rfl fun w (_ : w ∈ (univ : Finset V)) => pair_partition c hdiag v w
  simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one] at h
  simpa [hdeg, zdeg] using h

theorem gI_symm (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x) (x y : V) :
    gI c x y = gI c y x := by
  simp only [gI, ne_comm, hsymm x y]

/-! ### Ordered triangle count and the apex bound -/

/-- Ordered triangles of `H`: triples `(v,x,y)` with all three pairs red-or-blue.
This is `6 T(H)`. -/
def orderedTriangles (c : V → V → Colour) : ℕ :=
  ∑ v, ∑ x, ∑ y, isH (c v x) * isH (c v y) * isH (c x y)

/-- Ordered apex count at `v`: ordered pairs `(x,y)` with `vx, vy` of one of red and blue
and `xy` of the other. This is `2 (e_2(N_1(v)) + e_1(N_2(v)))`. -/
def apexCount (c : V → V → Colour) (v : V) : ℕ :=
  ∑ x, ∑ y, repeatedApex (c v x) (c v y) (c x y)

/-- Counting each triangle of `H` at its unique apex: `6 T(H) = 3 Σ_v apexCount v`. -/
theorem orderedTriangles_eq (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue) :
    orderedTriangles c = 3 * ∑ v, apexCount c v := by
  have h1 : orderedTriangles c = ∑ v, ∑ x, ∑ y,
      (repeatedApex (c v x) (c v y) (c x y) + repeatedApex (c v x) (c x y) (c v y) +
        repeatedApex (c v y) (c x y) (c v x)) := by
    unfold orderedTriangles
    refine sum_congr rfl fun v _ => sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    exact unique_repeated_apex _ _ _ (fun h => hred v x y h.1 h.2.1 h.2.2)
      (fun h => hblue v x y h.1 h.2.1 h.2.2)
  have h2 : ∑ v, ∑ x, ∑ y, repeatedApex (c v x) (c x y) (c v y) = ∑ v, apexCount c v := by
    rw [sum_comm]
    refine sum_congr rfl fun x _ => sum_congr rfl fun v _ => sum_congr rfl fun y _ => ?_
    rw [hsymm v x]
  have h3 : ∑ v, ∑ x, ∑ y, repeatedApex (c v y) (c x y) (c v x) = ∑ v, apexCount c v := by
    rw [show (∑ v, ∑ x, ∑ y, repeatedApex (c v y) (c x y) (c v x)) =
        ∑ v, ∑ y, ∑ x, repeatedApex (c v y) (c x y) (c v x) from
        sum_congr rfl fun v _ => sum_comm, sum_comm]
    refine sum_congr rfl fun y _ => sum_congr rfl fun v _ => sum_congr rfl fun x _ => ?_
    rw [hsymm v y, hsymm x y]
  rw [h1]
  simp only [sum_add_distrib]
  rw [h2, h3]
  simp only [apexCount]
  ring

theorem repeatedApex_split (a b d : Colour) :
    repeatedApex a b d = (if a = red ∧ b = red ∧ d = blue then 1 else 0) +
      (if a = blue ∧ b = blue ∧ d = red then 1 else 0) := by
  cases a <;> cases b <;> cases d <;> simp [repeatedApex]

/-- The apex count at `v` in terms of mixed neighbourhoods. -/
theorem apexCount_eq (c : V → V → Colour) (v : V) :
    apexCount c v = ∑ u ∈ neighbourhood c red v, (mixedNeighbourhood c v u).card +
      ∑ u ∈ neighbourhood c blue v, (mixedNeighbourhoodSwap c v u).card := by
  unfold apexCount
  simp only [repeatedApex_split, sum_add_distrib]
  congr 1
  · rw [neighbourhood, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    by_cases hx : c v x = red
    · simp [hx, mixedNeighbourhood]
    · simp [hx]
  · rw [neighbourhood, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    by_cases hx : c v x = blue
    · simp [hx, mixedNeighbourhoodSwap]
    · simp [hx]

/-- The local apex bound: `apexCount v ≤ (k-1) h_v`. -/
theorem apexCount_le (c : V → V → Colour) (k : ℕ)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue)
    (hgreen : AvoidsGreenK c k) (v : V) :
    apexCount c v ≤ (k - 1) * hdeg c v := by
  rw [apexCount_eq, hdeg_eq_red_add_blue]
  have h1 := local_ordered_edge_bound c k hred hblue hgreen v
  have h2 := local_ordered_edge_bound_swap c k hred hblue hgreen v
  nlinarith

/-- Equation `eq:apex6` without the bracket: `6 T(H) ≤ 3 (k-1) Σ_v h_v`. -/
theorem orderedTriangles_le (c : V → V → Colour) (k : ℕ) (hsymm : ∀ x y, c x y = c y x)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue)
    (hgreen : AvoidsGreenK c k) :
    orderedTriangles c ≤ 3 * (k - 1) * ∑ v, hdeg c v := by
  rw [orderedTriangles_eq c hsymm hred hblue]
  calc 3 * ∑ v, apexCount c v ≤ 3 * ∑ v, (k - 1) * hdeg c v :=
        Nat.mul_le_mul_left 3 (sum_le_sum fun v _ => apexCount_le c k hred hblue hgreen v)
    _ = 3 * (k - 1) * ∑ v, hdeg c v := by rw [← mul_sum, mul_assoc]

/-! ### Cliques and caps (Lemma `lem:caps`) -/

theorem isMonoClique_triple {c : V → V → Colour} (hsymm : ∀ x y, c x y = c y x) {a : Colour}
    {p q r : V} (h1 : c p q = a) (h2 : c p r = a) (h3 : c q r = a) :
    IsMonoClique c a {p, q, r} := by
  intro u hu w hw huw
  simp only [mem_insert, mem_singleton] at hu hw
  rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
    first | exact absurd rfl huw | assumption | (rw [hsymm]; assumption)

/-- A triangle-free colour has no `K_3` in any vertex set. -/
theorem noMonoK_three {c : V → V → Colour} {a : Colour} (h : NoMonoTriangle c a)
    (S : Finset V) : NoMonoK c a 3 S := by
  rintro ⟨T, -, hcard, hcl⟩
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp hcard
  exact h p q r (hcl p (by simp) q (by simp) hpq) (hcl p (by simp) r (by simp) hpr)
    (hcl q (by simp) r (by simp) hqr)

theorem noMonoK_of_avoidsGreenK {c : V → V → Colour} {k : ℕ} (h : AvoidsGreenK c k)
    (S : Finset V) : NoMonoK c green k S := by
  rintro ⟨T, -, hcard, hcl⟩
  have := h T hcl
  omega

/-- With a green diagonal, "no red `K_3`" in the usual sense gives the ordered convention
`NoMonoTriangle` of `RamseyLocal`. -/
theorem noMonoTriangle_of_noMonoK {c : V → V → Colour} (hsymm : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green) {a : Colour} (ha : a ≠ green) (h : NoMonoK c a 3 univ) :
    NoMonoTriangle c a := by
  intro v x y hvx hvy hxy
  have hne : ∀ p q, c p q = a → p ≠ q := by
    intro p q hpq heq
    subst heq
    exact ha (hpq.symm.trans (hdiag p))
  apply h
  refine ⟨{v, x, y}, subset_univ _, ?_, isMonoClique_triple hsymm hvx hvy hxy⟩
  rw [card_eq_three]
  exact ⟨v, x, y, hne _ _ hvx, hne _ _ hvy, hne _ _ hxy, rfl⟩

theorem avoidsGreenK_of_noMonoK {c : V → V → Colour} {k : ℕ} (h : NoMonoK c green k univ) :
    AvoidsGreenK c k := by
  intro T hT
  exact noMonoK_iff.mp h T (subset_univ _) hT

/-- Lemma `lem:caps`, `D_1`: the red neighbourhood `N_1(v)` carries a `(2,3,k)`-avoiding
colouring, so a cap on such sets bounds the red degree. -/
theorem red_degree_le {c : V → V → Colour} {k D : ℕ}
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue) (hgreen : AvoidsGreenK c k)
    (hcap : ∀ S : Finset V, AvoidsOn c 2 3 k S → S.card ≤ D) (v : V) :
    (neighbourhood c red v).card ≤ D := by
  apply hcap
  refine ⟨?_, noMonoK_three hblue _, noMonoK_of_avoidsGreenK hgreen _⟩
  rintro ⟨T, hTS, hcard, hcl⟩
  obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.mp hcard
  have hp : c v p = red := by
    have := hTS (by simp : p ∈ ({p, q} : Finset V)); simpa [neighbourhood] using this
  have hq : c v q = red := by
    have := hTS (by simp : q ∈ ({p, q} : Finset V)); simpa [neighbourhood] using this
  exact hred v p q hp hq (hcl p (by simp) q (by simp) hpq)

/-- Lemma `lem:caps`, `D_2`: the same for the blue neighbourhood and `(3,2,k)`. -/
theorem blue_degree_le {c : V → V → Colour} {k D : ℕ}
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue) (hgreen : AvoidsGreenK c k)
    (hcap : ∀ S : Finset V, AvoidsOn c 3 2 k S → S.card ≤ D) (v : V) :
    (neighbourhood c blue v).card ≤ D := by
  apply hcap
  refine ⟨noMonoK_three hred _, ?_, noMonoK_of_avoidsGreenK hgreen _⟩
  rintro ⟨T, hTS, hcard, hcl⟩
  obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.mp hcard
  have hp : c v p = blue := by
    have := hTS (by simp : p ∈ ({p, q} : Finset V)); simpa [neighbourhood] using this
  have hq : c v q = blue := by
    have := hTS (by simp : q ∈ ({p, q} : Finset V)); simpa [neighbourhood] using this
  exact hblue v p q hp hq (hcl p (by simp) q (by simp) hpq)

/-- Lemma `lem:caps` with `i = j = 3`: for a green edge `xy`, the common green neighbourhood
`N_3(x) ∩ N_3(y)` carries a `(3,3,k-2)`-avoiding colouring. -/
theorem avoidsOn_common_green {c : V → V → Colour} {k : ℕ} (hk : 2 ≤ k)
    (hsymm : ∀ x y, c x y = c y x)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue) (hgreen : AvoidsGreenK c k)
    {x y : V} (hxy : x ≠ y) (hg : c x y = green) :
    AvoidsOn c 3 3 (k - 2) (greenNbhd c x ∩ greenNbhd c y) := by
  refine ⟨noMonoK_three hred _, noMonoK_three hblue _, ?_⟩
  rintro ⟨T, hTS, hcard, hcl⟩
  have hmem : ∀ t ∈ T, (t ≠ x ∧ c x t = green) ∧ (t ≠ y ∧ c y t = green) := by
    intro t ht
    have := hTS ht
    rw [mem_inter, mem_greenNbhd, mem_greenNbhd] at this
    exact this
  have hxT : x ∉ T := fun h => (hmem x h).1.1 rfl
  have hyT : y ∉ T := fun h => (hmem y h).2.1 rfl
  have hx' : x ∉ insert y T := by simp [hxy, hxT]
  have hcard' : (insert x (insert y T)).card = k := by
    rw [card_insert_of_notMem hx', card_insert_of_notMem hyT]
    omega
  have hcl' : GreenClique c (insert x (insert y T)) := by
    intro p hp q hq hpq
    simp only [mem_insert] at hp hq
    rcases hp with rfl | rfl | hp <;> rcases hq with rfl | rfl | hq
    · exact absurd rfl hpq
    · exact hg
    · exact (hmem q hq).1.2
    · rw [hsymm]; exact hg
    · exact absurd rfl hpq
    · exact (hmem q hq).2.2
    · rw [hsymm]; exact (hmem p hp).1.2
    · rw [hsymm]; exact (hmem p hp).2.2
    · exact hcl p hp q hq hpq
  have := hgreen _ hcl'
  omega

/-! ### The cherry identity and the common-neighbour inequality (Lemma `lem:commonnbr`) -/

/-- `c_H(x,y)`, the number of common `H`-neighbours of `x` and `y`. -/
def commonH (c : V → V → Colour) (x y : V) : ℕ := ∑ v, isH (c v x) * isH (c v y)

/-- Ordered cherries `(x,v,y)` of `H` whose endpoints `x ≠ y` are joined in green. -/
def greenCherries (c : V → V → Colour) : ℕ :=
  ∑ v, ∑ x, ∑ y, isH (c v x) * isH (c v y) * gI c x y

/-- Step 1 of Lemma `lem:commonnbr`, doubled (ordered pairs):
`Σ_v h_v² = Σ_v h_v + 6 T(H) + Σ_{x≠y green} c_H(x,y)`. -/
theorem cherry_identity (c : V → V → Colour) (hdiag : ∀ v, c v v = green) :
    ∑ v, hdeg c v * hdeg c v = ∑ v, hdeg c v + orderedTriangles c + greenCherries c := by
  have hv : ∀ v, hdeg c v * hdeg c v = hdeg c v +
      ∑ x, ∑ y, isH (c v x) * isH (c v y) * isH (c x y) +
      ∑ x, ∑ y, isH (c v x) * isH (c v y) * gI c x y := by
    intro v
    have e1 : hdeg c v * hdeg c v = ∑ x, ∑ y, isH (c v x) * isH (c v y) *
        ((if x = y then 1 else 0) + isH (c x y) + gI c x y) := by
      simp only [pair_partition c hdiag, mul_one]
      rw [hdeg, sum_mul_sum]
    rw [e1]
    simp only [mul_add, sum_add_distrib]
    congr 2
    rw [hdeg]
    refine sum_congr rfl fun x _ => ?_
    simp [isH_mul_self]
  rw [sum_congr rfl fun v _ => hv v]
  simp only [sum_add_distrib, orderedTriangles, greenCherries]

theorem greenCherries_eq (c : V → V → Colour) :
    greenCherries c = ∑ x, ∑ y, gI c x y * commonH c x y := by
  unfold greenCherries commonH
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun v _ => by ring

/-- Step 2 of Lemma `lem:commonnbr` (inclusion–exclusion across a green edge `xy`):
`c_H(x,y) = h_x + h_y - (n-2) + |N_3(x) ∩ N_3(y)|`. -/
theorem commonH_add_card (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green) {x y : V} (hxy : x ≠ y) (hg : c x y = green) :
    commonH c x y + Fintype.card V =
      hdeg c x + hdeg c y + (greenNbhd c x ∩ greenNbhd c y).card + 2 := by
  have hcH : commonH c x y = ∑ w, isH (c x w) * isH (c y w) := by
    unfold commonH
    exact sum_congr rfl fun w _ => by rw [hsymm w x, hsymm w y]
  have hcard : (greenNbhd c x ∩ greenNbhd c y).card =
      ∑ w, if (w ≠ x ∧ c x w = green) ∧ (w ≠ y ∧ c y w = green) then 1 else 0 := by
    rw [← card_filter]
    congr 1
    ext w
    simp [greenNbhd]
  have hgyx : c y x = green := by rw [hsymm]; exact hg
  have hpt : ∀ w, (if w ≠ x ∧ w ≠ y then 1 else 0) + isH (c x w) * isH (c y w) =
      isH (c x w) + isH (c y w) +
        (if (w ≠ x ∧ c x w = green) ∧ (w ≠ y ∧ c y w = green) then 1 else 0) := by
    intro w
    by_cases hwx : w = x
    · subst hwx
      simp [hdiag, hgyx, isH]
    by_cases hwy : w = y
    · subst hwy
      simp [hdiag, hg, isH]
    cases c x w <;> cases c y w <;> simp [hwx, hwy, isH]
  have hpt2 : ∀ w, (if w ≠ x ∧ w ≠ y then 1 else 0) + (if w = x then 1 else 0) +
      (if w = y then 1 else 0) = 1 := by
    intro w
    by_cases hwx : w = x
    · subst hwx; simp [hxy]
    by_cases hwy : w = y
    · simp [hwy, Ne.symm hxy]
    simp [hwx, hwy]
  have hcount := sum_congr rfl fun w (_ : w ∈ (univ : Finset V)) => hpt2 w
  simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one,
    Finset.sum_ite_eq', mem_univ, if_true] at hcount
  have hsum := sum_congr rfl fun w (_ : w ∈ (univ : Finset V)) => hpt w
  simp only [sum_add_distrib] at hsum
  rw [hcH, hcard]
  unfold hdeg
  omega

/-- Steps 2–3 of Lemma `lem:commonnbr`: summing `eq:ie` over the (ordered) green edges,
`Σ c_H(x,y) ≤ Σ (h_x + h_y + U + 1 - n)`, written without subtraction. -/
theorem greenCherries_bound (c : V → V → Colour) (k U : ℕ) (hk : 2 ≤ k)
    (hsymm : ∀ x y, c x y = c y x) (hdiag : ∀ v, c v v = green)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue) (hgreen : AvoidsGreenK c k)
    (hU : ∀ S : Finset V, AvoidsOn c 3 3 (k - 2) S → S.card < U) :
    greenCherries c + Fintype.card V * ∑ v, zdeg c v ≤
      2 * ∑ v, hdeg c v * zdeg c v + (U + 1) * ∑ v, zdeg c v := by
  rw [greenCherries_eq]
  have hpt : ∀ x y, gI c x y * commonH c x y + Fintype.card V * gI c x y ≤
      gI c x y * hdeg c x + gI c x y * hdeg c y + (U + 1) * gI c x y := by
    intro x y
    by_cases h : x ≠ y ∧ c x y = green
    · have h1 := commonH_add_card c hsymm hdiag h.1 h.2
      have h2 := hU _ (avoidsOn_common_green hk hsymm hred hblue hgreen h.1 h.2)
      simp only [gI, if_pos h]
      omega
    · simp [gI, h]
  have hsum := sum_le_sum fun x (_ : x ∈ (univ : Finset V)) =>
    sum_le_sum fun y (_ : y ∈ (univ : Finset V)) => hpt x y
  simp only [sum_add_distrib] at hsum
  have e1 : ∑ x : V, ∑ y : V, Fintype.card V * gI c x y = Fintype.card V * ∑ v, zdeg c v := by
    simp only [zdeg, mul_sum]
  have e2 : ∑ x : V, ∑ y : V, gI c x y * hdeg c x = ∑ v, hdeg c v * zdeg c v := by
    refine sum_congr rfl fun x _ => ?_
    rw [zdeg, mul_sum]
    exact sum_congr rfl fun y _ => mul_comm _ _
  have e3 : ∑ x : V, ∑ y : V, gI c x y * hdeg c y = ∑ v, hdeg c v * zdeg c v := by
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [zdeg, mul_sum]
    exact sum_congr rfl fun x _ => by rw [gI_symm c hsymm x y, mul_comm]
  have e4 : ∑ x : V, ∑ y : V, (U + 1) * gI c x y = (U + 1) * ∑ v, zdeg c v := by
    simp only [zdeg, mul_sum]
  rw [e1, e2, e3, e4] at hsum
  linarith

/-- The part of `F` that does not involve the apex bound:
`G₀(h) = 3h² + (U+2-3n)h + (n-U-1)(n-1)`, so that `F = G₀ - 3(k-1)h`. -/
def G0 (n U : ℤ) (h : ℤ) : ℤ := 3 * h ^ 2 + (U + 2 - 3 * n) * h + (n - U - 1) * (n - 1)

/-- Steps 1–4 of Lemma `lem:commonnbr` before the apex bound is applied:
`Σ_v G₀(h_v) ≤ 6 T(H)` (ordered triangle count). -/
theorem cherry_bound (c : V → V → Colour) (k U : ℕ) (hk : 2 ≤ k)
    (hsymm : ∀ x y, c x y = c y x) (hdiag : ∀ v, c v v = green)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue) (hgreen : AvoidsGreenK c k)
    (hU : ∀ S : Finset V, AvoidsOn c 3 3 (k - 2) S → S.card < U) :
    ∑ v, G0 (Fintype.card V) U (hdeg c v) ≤ orderedTriangles c := by
  set n := Fintype.card V with hn
  have hz : ∀ v, (zdeg c v : ℤ) = n - 1 - hdeg c v := by
    intro v
    have := one_add_hdeg_add_zdeg c hdiag v
    rw [← hn] at this
    omega
  have hch := cherry_identity c hdiag
  have hG := greenCherries_bound c k U hk hsymm hdiag hred hblue hgreen hU
  have hch' : (∑ v, (hdeg c v : ℤ) * hdeg c v) =
      ∑ v, (hdeg c v : ℤ) + orderedTriangles c + greenCherries c := by exact_mod_cast hch
  have hG' : (greenCherries c : ℤ) + n * ∑ v, (zdeg c v : ℤ) ≤
      2 * ∑ v, (hdeg c v : ℤ) * zdeg c v + ((U : ℤ) + 1) * ∑ v, (zdeg c v : ℤ) := by
    exact_mod_cast hG
  have hF : ∑ v, G0 n U (hdeg c v) = ∑ v, ((hdeg c v : ℤ) * hdeg c v - hdeg c v -
      2 * ((hdeg c v : ℤ) * zdeg c v) - ((U : ℤ) + 1) * zdeg c v + (n : ℤ) * zdeg c v) := by
    refine sum_congr rfl fun v _ => ?_
    rw [hz v]
    unfold G0
    ring
  rw [hF]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  linarith

/-- The function `F_{n,k,U}` of Lemma `lem:commonnbr` (without the bracket). -/
def F (n k U : ℤ) (h : ℤ) : ℤ := 3 * h ^ 2 + (U + 5 - 3 * n - 3 * k) * h + (n - U - 1) * (n - 1)

theorem F_eq_G0 (n k U h : ℤ) : F n k U h = G0 n U h - 3 * (k - 1) * h := by
  unfold F G0; ring

/-- Lemma `lem:commonnbr`, without the bracket, in terms of the indicator degrees. -/
theorem commonnbr_hdeg (c : V → V → Colour) (k U : ℕ) (hk : 2 ≤ k)
    (hsymm : ∀ x y, c x y = c y x) (hdiag : ∀ v, c v v = green)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue) (hgreen : AvoidsGreenK c k)
    (hU : ∀ S : Finset V, AvoidsOn c 3 3 (k - 2) S → S.card < U) :
    ∑ v, F (Fintype.card V) k U (hdeg c v) ≤ 0 := by
  have h0 := cherry_bound c k U hk hsymm hdiag hred hblue hgreen hU
  have hT := orderedTriangles_le c k hsymm hred hblue hgreen
  have hk1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]; simp
  have hT' : (orderedTriangles c : ℤ) ≤ 3 * ((k : ℤ) - 1) * ∑ v, (hdeg c v : ℤ) := by
    rw [← hk1]; exact_mod_cast hT
  simp only [F_eq_G0, sum_sub_distrib, ← mul_sum]
  linarith

end Internal

section Apex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### `T(H)` and Lemma `lem:apex` with `A_k` -/

/-- In any finite simple graph, ordered triangles `(a,b,c)` number `6` times the triangles
(`3`-cliques). -/
theorem card_orderedTriangles_graph (G : SimpleGraph V) [DecidableRel G.Adj] :
    (univ.filter fun p : V × V × V => G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2).card
      = 6 * (G.cliqueFinset 3).card := by
  set P := univ.filter fun p : V × V × V =>
    G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2 with hP
  have hmaps : ∀ p ∈ P, ({p.1, p.2.1, p.2.2} : Finset V) ∈ G.cliqueFinset 3 := by
    intro p hp
    rw [hP, mem_filter] at hp
    rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_triple_iff]
    exact hp.2
  rw [card_eq_sum_card_fiberwise hmaps, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun s hs => ?_
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
    SimpleGraph.is3Clique_iff.mp (SimpleGraph.mem_cliqueFinset_iff.mp hs)
  have nab := G.ne_of_adj hab
  have nac := G.ne_of_adj hac
  have nbc := G.ne_of_adj hbc
  have hfib : P.filter (fun p => ({p.1, p.2.1, p.2.2} : Finset V) = {a, b, c}) =
      {(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)} := by
    ext ⟨x, y, z⟩
    simp only [hP, mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hxy, hxz, hyz⟩, hset⟩
      have hx : x ∈ ({a, b, c} : Finset V) := by rw [← hset]; simp
      have hy : y ∈ ({a, b, c} : Finset V) := by rw [← hset]; simp
      have hz : z ∈ ({a, b, c} : Finset V) := by rw [← hset]; simp
      have h1 := G.ne_of_adj hxy
      have h2 := G.ne_of_adj hxz
      have h3 := G.ne_of_adj hyz
      simp only [mem_insert, mem_singleton] at hx hy hz
      clear hset hxy hxz hyz
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        rcases hz with rfl | rfl | rfl <;>
        first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | simp
    · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;>
        first
          | assumption
          | exact hab.symm
          | exact hac.symm
          | exact hbc.symm
          | (ext w; simp only [mem_insert, mem_singleton]; try tauto)
  rw [hfib]
  rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem,
    card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  all_goals simp [nab, nac, nbc, Ne.symm nab, Ne.symm nac, Ne.symm nbc]

/-- `6 T(H)` is the ordered triangle count, where `T(H)` is the number of triangles
(`3`-cliques) of the merged graph `H`. -/
theorem orderedTriangles_eq_six_mul (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green) :
    orderedTriangles c = 6 * ((mergedGraph c hsymm hdiag).cliqueFinset 3).card := by
  rw [← card_orderedTriangles_graph, card_filter, Fintype.sum_prod_type]
  unfold orderedTriangles
  refine sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  cases h1 : c v x <;> cases h2 : c v y <;> cases h3 : c x y <;>
    simp [isH, mergedGraph, h1, h2, h3]

/-- The graph of colour-`b` edges inside the colour-`a` neighbourhood `N_a(v)`. -/
def insideGraph (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green) (a b : Colour) (hb : b ≠ green) (v : V) : SimpleGraph V where
  Adj x y := c v x = a ∧ c v y = a ∧ c x y = b
  symm := fun x y (h : c v x = a ∧ c v y = a ∧ c x y = b) =>
    (show c v y = a ∧ c v x = a ∧ c y x = b from ⟨h.2.1, h.1, by rw [hsymm]; exact h.2.2⟩)
  loopless := fun x (h : c v x = a ∧ c v x = a ∧ c x x = b) => hb (h.2.2.symm.trans (hdiag x))

instance insideGraph.decRel (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green) (a b : Colour) (hb : b ≠ green) (v : V) :
    DecidableRel (insideGraph c hsymm hdiag a b hb v).Adj :=
  fun x y => inferInstanceAs (Decidable (c v x = a ∧ c v y = a ∧ c x y = b))

/-- `e_b(N_a(v))`, the number of colour-`b` edges inside `N_a(v)`. -/
def edgesInside (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green) (a b : Colour) (hb : b ≠ green) (v : V) : ℕ :=
  (insideGraph c hsymm hdiag a b hb v).edgeFinset.card

/-- Handshake lemma for `e_2(N_1(v))`. -/
theorem two_mul_edgesInside_red (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green) (v : V) :
    2 * edgesInside c hsymm hdiag red blue (by decide) v =
      ∑ u ∈ neighbourhood c red v, (mixedNeighbourhood c v u).card := by
  rw [edgesInside, ← SimpleGraph.sum_degrees_eq_twice_card_edges, neighbourhood, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  by_cases hx : c v x = red
  · simp [insideGraph, hx, mixedNeighbourhood]
  · simp [insideGraph, hx]

/-- Handshake lemma for `e_1(N_2(v))`. -/
theorem two_mul_edgesInside_blue (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green) (v : V) :
    2 * edgesInside c hsymm hdiag blue red (by decide) v =
      ∑ u ∈ neighbourhood c blue v, (mixedNeighbourhoodSwap c v u).card := by
  rw [edgesInside, ← SimpleGraph.sum_degrees_eq_twice_card_edges, neighbourhood, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  by_cases hx : c v x = blue
  · simp [insideGraph, hx, mixedNeighbourhoodSwap]
  · simp [insideGraph, hx]

/-- The display before Lemma `lem:apex`: counting each triangle of `H` at its apex,
`T(H) = Σ_v (e_2(N_1(v)) + e_1(N_2(v)))`. -/
theorem triangles_eq_sum_edgesInside (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue) :
    ((mergedGraph c hsymm hdiag).cliqueFinset 3).card =
      ∑ v, (edgesInside c hsymm hdiag red blue (by decide) v +
        edgesInside c hsymm hdiag blue red (by decide) v) := by
  have h1 := orderedTriangles_eq_six_mul c hsymm hdiag
  have h2 := orderedTriangles_eq c hsymm hred hblue
  have h3 : ∑ v, apexCount c v = 2 * ∑ v, (edgesInside c hsymm hdiag red blue (by decide) v +
      edgesInside c hsymm hdiag blue red (by decide) v) := by
    rw [mul_sum]
    refine sum_congr rfl fun v _ => ?_
    rw [apexCount_eq, mul_add, two_mul_edgesInside_red, two_mul_edgesInside_blue]
  omega

/-- The function `A_k` of Lemma `lem:apex` (for `0 ≤ h ≤ 2D`): `⌊(k-1)h/2⌋`, except
`A_k(2D) = (k-1)D - 1` when `k` is even and `D` is odd. -/
def apexA (k D h : ℕ) : ℕ :=
  if k % 2 = 0 ∧ D % 2 = 1 ∧ h = 2 * D then (k - 1) * D - 1 else (k - 1) * h / 2

theorem add_le_apexA {k D d₁ d₂ e₁ e₂ : ℕ} (hd₁ : d₁ ≤ D) (hd₂ : d₂ ≤ D)
    (he₁ : 2 * e₁ ≤ (k - 1) * d₁) (he₂ : 2 * e₂ ≤ (k - 1) * d₂) :
    e₁ + e₂ ≤ apexA k D (d₁ + d₂) := by
  unfold apexA
  split_ifs with h
  · obtain ⟨hk, hD, hsum⟩ := h
    have h1 : d₁ = D := by omega
    have h2 : d₂ = D := by omega
    rw [h1] at he₁
    rw [h2] at he₂
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simp at he₁ he₂
      omega
    · have hodd : ((k - 1) * D) % 2 = 1 := by
        rw [Nat.mul_mod]
        have : (k - 1) % 2 = 1 := by omega
        rw [this, hD]
      generalize (k - 1) * D = m at *
      omega
  · have : (k - 1) * (d₁ + d₂) = (k - 1) * d₁ + (k - 1) * d₂ := mul_add _ _ _
    rw [this]
    generalize (k - 1) * d₁ = m₁ at *
    generalize (k - 1) * d₂ = m₂ at *
    omega

theorem two_mul_apexA_le (k D h : ℕ) : 2 * apexA k D h ≤ (k - 1) * h := by
  unfold apexA
  split_ifs with hh
  · obtain ⟨-, -, rfl⟩ := hh
    have : (k - 1) * (2 * D) = 2 * ((k - 1) * D) := by ring
    rw [this]
    generalize (k - 1) * D = m
    omega
  · generalize (k - 1) * h = m
    omega

/-- **Lemma `lem:apex`.** For a `(3,3,k;n)`-colouring whose red and blue degrees are capped
by `D` (encoded, as in Lemma `lem:caps`, by caps on `(2,3,k)`- and `(3,2,k)`-avoiding vertex
sets), `T(H) ≤ Σ_v A_k(h_v)` and `Σ_v A_k(h_v) ≤ ((k-1)/2) Σ_v h_v`. -/
theorem apex_bound (c : V → V → Colour) (k D : ℕ) (hsymm : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green) (hav : AvoidsOn c 3 3 k univ)
    (hD₁ : ∀ S : Finset V, AvoidsOn c 2 3 k S → S.card ≤ D)
    (hD₂ : ∀ S : Finset V, AvoidsOn c 3 2 k S → S.card ≤ D) :
    ((mergedGraph c hsymm hdiag).cliqueFinset 3).card ≤
        ∑ v, apexA k D ((mergedGraph c hsymm hdiag).degree v) ∧
      2 * ∑ v, apexA k D ((mergedGraph c hsymm hdiag).degree v) ≤
        (k - 1) * ∑ v, (mergedGraph c hsymm hdiag).degree v := by
  have hred := noMonoTriangle_of_noMonoK hsymm hdiag (by decide) hav.1
  have hblue := noMonoTriangle_of_noMonoK hsymm hdiag (by decide) hav.2.1
  have hgreen := avoidsGreenK_of_noMonoK hav.2.2
  constructor
  · rw [triangles_eq_sum_edgesInside c hsymm hdiag hred hblue]
    refine sum_le_sum fun v _ => ?_
    rw [mergedGraph_degree, hdeg_eq_red_add_blue]
    apply add_le_apexA (red_degree_le hred hblue hgreen hD₁ v)
      (blue_degree_le hred hblue hgreen hD₂ v)
    · rw [two_mul_edgesInside_red, mul_comm (k - 1)]
      exact local_ordered_edge_bound c k hred hblue hgreen v
    · rw [two_mul_edgesInside_blue, mul_comm (k - 1)]
      exact local_ordered_edge_bound_swap c k hred hblue hgreen v
  · rw [mul_sum, mul_sum]
    exact sum_le_sum fun v _ => two_mul_apexA_le k D _

/-- `p_k(h) = 3(k-1)h - 6 A_k(h)`, six times the gap in Lemma `lem:apex`. -/
def pk (k D h : ℕ) : ℤ := 3 * ((k : ℤ) - 1) * h - 6 * (apexA k D h : ℤ)

theorem pk_nonneg {k : ℕ} (hk : 1 ≤ k) (D h : ℕ) : 0 ≤ pk k D h := by
  have h1 := two_mul_apexA_le k D h
  have h2 : ((2 * apexA k D h : ℕ) : ℤ) ≤ (((k - 1) * h : ℕ) : ℤ) := by exact_mod_cast h1
  push_cast [Nat.cast_sub hk] at h2
  unfold pk
  linarith

/-- **Lemma `lem:commonnbr`** (without the bracket), for the merged graph `H` of a
`(3,3,k;n)`-colouring, `k ≥ 2`, with `U ≥ R(3,3,k-2)` encoded as the cap "every
`(3,3,k-2)`-avoiding vertex set has fewer than `U` vertices":
`Σ_v F_{n,k,U}(h_v) ≤ 0`. -/
theorem commonnbr (c : V → V → Colour) (k U : ℕ) (hk : 2 ≤ k)
    (hsymm : ∀ x y, c x y = c y x) (hdiag : ∀ v, c v v = green)
    (hav : AvoidsOn c 3 3 k univ)
    (hU : ∀ S : Finset V, AvoidsOn c 3 3 (k - 2) S → S.card < U) :
    ∑ v, F (Fintype.card V) k U ((mergedGraph c hsymm hdiag).degree v) ≤ 0 := by
  simp only [mergedGraph_degree]
  exact commonnbr_hdeg c k U hk hsymm hdiag
    (noMonoTriangle_of_noMonoK hsymm hdiag (by decide) hav.1)
    (noMonoTriangle_of_noMonoK hsymm hdiag (by decide) hav.2.1)
    (avoidsGreenK_of_noMonoK hav.2.2) hU

/-- **Lemma `lem:commonnbr` with the bracket:** `Σ_v (F_{n,k,U}(h_v) + p_k(h_v)) ≤ 0`,
where `p_k` uses the red/blue degree cap `D`. -/
theorem commonnbr_bracket (c : V → V → Colour) (k U D : ℕ) (hk : 2 ≤ k)
    (hsymm : ∀ x y, c x y = c y x) (hdiag : ∀ v, c v v = green)
    (hav : AvoidsOn c 3 3 k univ)
    (hU : ∀ S : Finset V, AvoidsOn c 3 3 (k - 2) S → S.card < U)
    (hD₁ : ∀ S : Finset V, AvoidsOn c 2 3 k S → S.card ≤ D)
    (hD₂ : ∀ S : Finset V, AvoidsOn c 3 2 k S → S.card ≤ D) :
    ∑ v, (F (Fintype.card V) k U ((mergedGraph c hsymm hdiag).degree v) +
      pk k D ((mergedGraph c hsymm hdiag).degree v)) ≤ 0 := by
  have hred := noMonoTriangle_of_noMonoK hsymm hdiag (by decide) hav.1
  have hblue := noMonoTriangle_of_noMonoK hsymm hdiag (by decide) hav.2.1
  have hgreen := avoidsGreenK_of_noMonoK hav.2.2
  have h0 := cherry_bound c k U hk hsymm hdiag hred hblue hgreen hU
  have hT := (apex_bound c k D hsymm hdiag hav hD₁ hD₂).1
  have h6 := orderedTriangles_eq_six_mul c hsymm hdiag
  simp only [mergedGraph_degree] at hT ⊢
  have hT' : (orderedTriangles c : ℤ) ≤ 6 * ∑ v, (apexA k D (hdeg c v) : ℤ) := by
    rw [h6]; push_cast; exact_mod_cast Nat.mul_le_mul_left 6 hT
  have hpt : ∀ v, F (Fintype.card V) k U (hdeg c v) + pk k D (hdeg c v) =
      G0 (Fintype.card V) U (hdeg c v) - 6 * (apexA k D (hdeg c v) : ℤ) := by
    intro v; rw [F_eq_G0]; unfold pk; ring
  simp only [hpt, sum_sub_distrib, ← mul_sum]
  linarith

/-! ### Admissible degrees -/

/-- `h` is admissible: `max(0, n-1-D₃) ≤ h ≤ min(n-1, 2D)` (natural subtraction gives the
`max(0, ·)`). -/
def Admissible (n D D₃ h : ℕ) : Prop := n - 1 - D₃ ≤ h ∧ h ≤ n - 1 ∧ h ≤ 2 * D

/-- Every `H`-degree is admissible, given the caps `D` (from `(2,3,k)`, `(3,2,k)`) and
`D₃` (from `(3,3,k-1)`), as in Lemma `lem:caps`. -/
theorem degree_admissible (c : V → V → Colour) (k D D₃ : ℕ) (hk : 1 ≤ k)
    (hsymm : ∀ x y, c x y = c y x) (hdiag : ∀ v, c v v = green)
    (hav : AvoidsOn c 3 3 k univ)
    (hD₁ : ∀ S : Finset V, AvoidsOn c 2 3 k S → S.card ≤ D)
    (hD₂ : ∀ S : Finset V, AvoidsOn c 3 2 k S → S.card ≤ D)
    (hD₃ : ∀ S : Finset V, AvoidsOn c 3 3 (k - 1) S → S.card ≤ D₃) (v : V) :
    Admissible (Fintype.card V) D D₃ ((mergedGraph c hsymm hdiag).degree v) := by
  have hred := noMonoTriangle_of_noMonoK hsymm hdiag (by decide) hav.1
  have hblue := noMonoTriangle_of_noMonoK hsymm hdiag (by decide) hav.2.1
  have hgreen := avoidsGreenK_of_noMonoK hav.2.2
  rw [mergedGraph_degree]
  have hn := one_add_hdeg_add_zdeg c hdiag v
  have h1 := red_degree_le hred hblue hgreen hD₁ v
  have h2 := blue_degree_le hred hblue hgreen hD₂ v
  have hz : zdeg c v = (greenNbhd c v).card := by
    rw [zdeg, greenNbhd, card_filter]
    refine sum_congr rfl fun w _ => ?_
    simp [gI, ne_comm]
  have h3 : (greenNbhd c v).card ≤ D₃ := by
    apply hD₃
    refine ⟨noMonoK_three hred _, noMonoK_three hblue _, ?_⟩
    rintro ⟨T, hTS, hcard, hcl⟩
    have hmem : ∀ t ∈ T, t ≠ v ∧ c v t = green := fun t ht => mem_greenNbhd.mp (hTS ht)
    have hvT : v ∉ T := fun h => (hmem v h).1 rfl
    have hcl' : GreenClique c (insert v T) := by
      intro p hp q hq hpq
      simp only [mem_insert] at hp hq
      rcases hp with rfl | hp <;> rcases hq with rfl | hq
      · exact absurd rfl hpq
      · exact (hmem q hq).2
      · rw [hsymm]; exact (hmem p hp).2
      · exact hcl p hp q hq hpq
    have := hgreen _ hcl'
    rw [card_insert_of_notMem hvT] at this
    omega
  rw [hdeg_eq_red_add_blue] at hn ⊢
  refine ⟨?_, ?_, ?_⟩ <;> omega

end Apex

section Main

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Lemma `lem:line`(b), positivity, and Theorem `thm:336` -/

/-- Lemma `lem:line`(b): if `Σ_v f(h_v) ≤ 0` over a nonempty vertex set, then `f` cannot be
positive at every value that the `h_v` take. -/
theorem line_b {ι : Type*} [Fintype ι] [Nonempty ι] (f : ℤ → ℤ) (h : ι → ℕ) (P : ℕ → Prop)
    (hsum : ∑ v, f (h v) ≤ 0) (hP : ∀ v, P (h v)) (hpos : ∀ x, P x → 0 < f x) : False := by
  have : 0 < ∑ v, f (h v) := Finset.sum_pos (fun v _ => hpos _ (hP v)) univ_nonempty
  linarith

/-- Step 2 of the proof of `thm:336`: `F_{88,6,30}(h) = 3h² - 247h + 4959`. -/
theorem F_88_6_30 (h : ℤ) : F 88 6 30 h = 3 * h ^ 2 - 247 * h + 4959 := by
  unfold F; ring

/-- Step 3 of the proof of `thm:336`: with `x = 34 - h`, `F = 29 + 43x + 3x²`. -/
theorem F_88_6_30_shift (h : ℤ) : F 88 6 30 h = 29 + 43 * (34 - h) + 3 * (34 - h) ^ 2 := by
  unfold F; ring

theorem F_88_6_30_pos {h : ℕ} (hh : h ≤ 34) : 0 < F 88 6 30 h := by
  rw [F_88_6_30_shift]
  have hx : (0 : ℤ) ≤ 34 - h := by omega
  nlinarith [sq_nonneg ((34 : ℤ) - h)]

/-- Step 3 of `thm:336` stated on admissible degrees (any green cap `D₃`): `F_{88,6,30}` is
positive at every admissible `h` for `D = 17`. -/
theorem F_88_6_30_pos_of_admissible (D₃ h : ℕ) (hh : Admissible 88 17 D₃ h) :
    0 < F 88 6 30 h :=
  F_88_6_30_pos hh.2.2

/-- **Theorem `thm:336`, core form** (colouring with green diagonal).
A symmetric 3-colouring of `K_88` with no red `K_3`, no blue `K_3` and no green `K_6`
cannot exist, given the three caps:
* every vertex set with no red edge, no blue triangle and no green `K_6` has at most 17
  vertices (`R(2,3,6) = R(3,6) = 18`),
* the same with red and blue interchanged (`R(3,2,6) = R(3,6) = 18`),
* every vertex set with no red triangle, no blue triangle and no green `K_4` has at most 29
  vertices (`R(3,3,4) = 30`). -/
theorem r336_greenDiag (c : V → V → Colour) (hn : Fintype.card V = 88)
    (hsymm : ∀ x y, c x y = c y x) (hdiag : ∀ v, c v v = green)
    (hav : AvoidsOn c 3 3 6 univ)
    (hD1 : ∀ S : Finset V, AvoidsOn c 2 3 6 S → S.card ≤ 17)
    (hD2 : ∀ S : Finset V, AvoidsOn c 3 2 6 S → S.card ≤ 17)
    (hU : ∀ S : Finset V, AvoidsOn c 3 3 4 S → S.card ≤ 29) : False := by
  -- Step 1: the degree cap `h_v ≤ 2D = 34`, from `D = R(3,6) - 1 = 17` (Lemma `lem:caps`).
  have hle : ∀ v, (mergedGraph c hsymm hdiag).degree v ≤ 34 := by
    intro v
    have hred := noMonoTriangle_of_noMonoK hsymm hdiag (by decide) hav.1
    have hblue := noMonoTriangle_of_noMonoK hsymm hdiag (by decide) hav.2.1
    have hgreen := avoidsGreenK_of_noMonoK hav.2.2
    rw [mergedGraph_degree, hdeg_eq_red_add_blue]
    have h1 := red_degree_le hred hblue hgreen hD1 v
    have h2 := blue_degree_le hred hblue hgreen hD2 v
    omega
  -- Step 2: Lemma `lem:commonnbr` with `n = 88`, `k = 6`, `U = R(3,3,4) = 30`,
  -- without the bracket, so `F(h) = 3h² - 247h + 4959`.
  have hineq := commonnbr c 6 30 (by norm_num) hsymm hdiag hav
    (fun S hS => Nat.lt_succ_of_le (hU S hS))
  rw [hn] at hineq
  simp only [Nat.cast_ofNat] at hineq
  -- Step 3: `F = 29 + 43x + 3x² > 0` for `x = 34 - h ≥ 0`, and Lemma `lem:line`(b).
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  simp only [mergedGraph_degree] at hineq hle
  exact line_b (F 88 6 30) (hdeg c) (· ≤ 34) hineq hle (fun x hx => F_88_6_30_pos hx)

/-- Lemma `lem:apex` specialised to `k = 6`, `D = R(3,6) - 1 = 17`: here `k` is even and `D`
odd, so `A_6(34) = 5·17 - 1 = 84` and `A_6(h) = ⌊5h/2⌋` otherwise. -/
theorem apex_bound_k6 (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green) (hav : AvoidsOn c 3 3 6 univ)
    (hD1 : ∀ S : Finset V, AvoidsOn c 2 3 6 S → S.card ≤ 17)
    (hD2 : ∀ S : Finset V, AvoidsOn c 3 2 6 S → S.card ≤ 17) :
    ((mergedGraph c hsymm hdiag).cliqueFinset 3).card ≤
      ∑ v, apexA 6 17 ((mergedGraph c hsymm hdiag).degree v) :=
  (apex_bound c 6 17 hsymm hdiag hav hD1 hD2).1

theorem apexA_6_17 (h : ℕ) : apexA 6 17 h = if h = 34 then 84 else 5 * h / 2 := by
  unfold apexA
  by_cases hh : h = 34 <;> simp [hh]

/-- Setting the (irrelevant) diagonal of a colouring to green. -/
def diagGreen (c : V → V → Colour) : V → V → Colour := fun x y => if x = y then green else c x y

theorem isMonoClique_diagGreen {c : V → V → Colour} {a : Colour} {T : Finset V} :
    IsMonoClique (diagGreen c) a T ↔ IsMonoClique c a T := by
  constructor
  · intro h x hx y hy hxy
    have := h x hx y hy hxy
    simpa [diagGreen, hxy] using this
  · intro h x hx y hy hxy
    simpa [diagGreen, hxy] using h x hx y hy hxy

theorem avoidsOn_diagGreen {c : V → V → Colour} {s₁ s₂ s₃ : ℕ} {S : Finset V} :
    AvoidsOn (diagGreen c) s₁ s₂ s₃ S ↔ AvoidsOn c s₁ s₂ s₃ S := by
  simp only [AvoidsOn, NoMonoK, isMonoClique_diagGreen]

/-- **Theorem `thm:336`** (`R(3,3,6) ≤ 88`), for an arbitrary symmetric colouring of the
edges of `K_88` (the diagonal values play no role), under the three cap hypotheses that encode
`R(3,6) = 18` (twice, once per colour) and `R(3,3,4) = 30`. -/
theorem r336 (c : V → V → Colour) (hn : Fintype.card V = 88)
    (hsymm : ∀ x y, c x y = c y x)
    (hav : AvoidsOn c 3 3 6 univ)
    (hD1 : ∀ S : Finset V, AvoidsOn c 2 3 6 S → S.card ≤ 17)
    (hD2 : ∀ S : Finset V, AvoidsOn c 3 2 6 S → S.card ≤ 17)
    (hU : ∀ S : Finset V, AvoidsOn c 3 3 4 S → S.card ≤ 29) : False := by
  refine r336_greenDiag (diagGreen c) hn ?_ ?_ (avoidsOn_diagGreen.mpr hav)
    (fun S hS => hD1 S (avoidsOn_diagGreen.mp hS))
    (fun S hS => hD2 S (avoidsOn_diagGreen.mp hS))
    (fun S hS => hU S (avoidsOn_diagGreen.mp hS))
  · intro x y
    by_cases h : x = y
    · subst h; rfl
    · simp [diagGreen, h, Ne.symm h, hsymm x y]
  · intro v
    simp [diagGreen]

end Main

/-- **Theorem `thm:336` from conventional Ramsey bounds:** `R(3,6) ≤ 18` (two colours) and
`R(3,3,4) ≤ 30` imply `R(3,3,6) ≤ 88`. -/
theorem ramseyLE_336_88 (h36 : RamseyLE2 3 6 18) (h334 : RamseyLE 3 3 4 30) :
    RamseyLE 3 3 6 88 := by
  intro c hsymm hav
  have h1 : RamseyLE 2 3 6 18 := ramseyLE_of_ramseyLE2 h36
  have h2 : RamseyLE 3 2 6 18 := ramseyLE_swap h1
  exact r336 c (by simp) hsymm hav
    (fun S hS => Nat.lt_succ_iff.mp (card_lt_of_ramseyLE h1 c hsymm S hS))
    (fun S hS => Nat.lt_succ_iff.mp (card_lt_of_ramseyLE h2 c hsymm S hS))
    (fun S hS => Nat.lt_succ_iff.mp (card_lt_of_ramseyLE h334 c hsymm S hS))


#print axioms card_lt_of_ramseyLE
#print axioms triangles_eq_sum_edgesInside
#print axioms apex_bound
#print axioms apex_bound_k6
#print axioms commonnbr
#print axioms commonnbr_bracket
#print axioms degree_admissible
#print axioms F_88_6_30_pos
#print axioms r336_greenDiag
#print axioms r336
#print axioms ramseyLE_336_88

end RamseyLean.R336
