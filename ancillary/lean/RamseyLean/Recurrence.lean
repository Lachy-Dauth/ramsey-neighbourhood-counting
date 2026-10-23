import Mathlib

/-!
# The neighbourhood recurrence, its parity refinement, and Corollary `cor:four`

Paper: `paper/neighbourhood_counting.tex`.

* Equation `eq:recurrence` (Introduction, paragraph "The neighbourhood recurrence") and the
  parity refinement (paragraph "Parity and other improvements"), together with the
  `r`-colour form stated in Subsection `sec:four` ("The four-colour recurrence").
* Corollary `cor:four`: `R(3,3,4,4) ≤ 442`, `R(3,4,4,4) ≤ 1521`, `R(4,4,4,4) ≤ 6082`,
  from the inputs `R(3,4,4) ≤ 73`, `R(4,4,4) ≤ 198` and `R(3,3,3,4) ≤ 149`.

The file has two layers.

1. *Counting layer.*  For a symmetric colouring `c : V → V → ι` of the complete graph on a
   finite vertex set `V` and explicit caps `D i` on every colour-`i` neighbourhood,
   `|V| - 1 ≤ ∑ i, D i` (`recurrence_count`), and the order `|V| = ∑ i, D i + 1` is impossible
   when `∑ i, D i` is even and some `D i` is odd (`parity_obstruction`, via the handshake
   lemma).  No Ramsey number appears.

2. *Ramsey layer.*  `RamseyBound t B` says: every symmetric `ι`-colouring of a complete graph
   with no colour-`i` clique on `t i` vertices (for every `i`) has fewer than `B` vertices.
   This is exactly `R(t) ≤ B`; `ramseyBound_iff_fin` proves it equivalent to the textbook
   definition "every `ι`-colouring of the edges of `K_B` has, for some `i`, a colour-`i`
   clique on `t i` vertices".  Ramsey inputs enter only as hypotheses of this form.
   The recurrence derives `RamseyBound t _` from `RamseyBound (t - e_i) _` for all `i`.

Diagonal values `c v v` play no role: neighbourhoods exclude `v`, and cliques only constrain
pairs of distinct vertices.
-/

namespace RamseyLean.Recurrence

open Finset

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The colour-`i` neighbourhood `N_i(v)` of `v`: the vertices `w ≠ v` with `c v w = i`. -/
def nbhd (c : V → V → ι) (i : ι) (v : V) : Finset V :=
  (univ.erase v).filter (fun w => c v w = i)

omit [Fintype ι] in
theorem mem_nbhd {c : V → V → ι} {i : ι} {v w : V} :
    w ∈ nbhd c i v ↔ w ≠ v ∧ c v w = i := by
  simp [nbhd]

/-- The colour neighbourhoods of `v` partition the other `|V| - 1` vertices:
`d_1(v) + ⋯ + d_r(v) = n - 1`. -/
theorem sum_card_nbhd (c : V → V → ι) (v : V) :
    ∑ i, (nbhd c i v).card = Fintype.card V - 1 := by
  have h := Finset.card_eq_sum_card_fiberwise (f := c v) (s := univ.erase v) (t := univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at h
  rw [h]
  rfl

/-- **Neighbourhood recurrence, counting form.**  If in a colouring of `K_n` every colour-`i`
neighbourhood has at most `D i` vertices, then `n - 1 ≤ ∑ i, D i`
(stated without truncated subtraction as `n ≤ ∑ i, D i + 1`). -/
theorem recurrence_count (c : V → V → ι) (D : ι → ℕ)
    (hcap : ∀ v i, (nbhd c i v).card ≤ D i) :
    Fintype.card V ≤ ∑ i, D i + 1 := by
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v⟩⟩
  · simp
  · have h1 := sum_card_nbhd c v
    have h2 : ∑ i, (nbhd c i v).card ≤ ∑ i, D i :=
      Finset.sum_le_sum (fun i _ => hcap v i)
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    omega

omit [Fintype ι] in
/-- **Handshake lemma** for one colour class of a symmetric colouring:
the colour-`i` degrees have even sum. -/
theorem handshake (c : V → V → ι) (hsymm : ∀ x y, c x y = c y x) (i : ι) :
    Even (∑ v, (nbhd c i v).card) := by
  classical
  let G : SimpleGraph V := SimpleGraph.fromRel (fun a b => c a b = i)
  have hdeg : ∀ v, G.degree v = (nbhd c i v).card := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext w
    rw [SimpleGraph.mem_neighborFinset, mem_nbhd]
    simp only [G, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne, h | h⟩
      · exact ⟨Ne.symm hne, h⟩
      · exact ⟨Ne.symm hne, (hsymm v w).trans h⟩
    · rintro ⟨hne, h⟩
      exact ⟨Ne.symm hne, Or.inl h⟩
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges G
  simp only [hdeg] at h
  rw [h]
  exact even_two_mul _

/-- At the order `n = ∑ i, D i + 1` every cap is attained: `d_i(v) = D i` for all `v`, `i`. -/
theorem caps_tight (c : V → V → ι) (D : ι → ℕ)
    (hcap : ∀ v i, (nbhd c i v).card ≤ D i)
    (hn : Fintype.card V = ∑ i, D i + 1) (v : V) (i : ι) :
    (nbhd c i v).card = D i := by
  have h1 := sum_card_nbhd c v
  have heq : ∑ j, (nbhd c j v).card = ∑ j, D j := by omega
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hcap v j)).mp heq i (Finset.mem_univ i)

/-- **Parity obstruction.**  The order `n = ∑ i, D i + 1` (one below the right-hand side
`∑ i, (D i + 1) - (r - 2) = ∑ i, D i + 2` of the recurrence) is impossible when `n` is odd,
i.e. `∑ i, D i` is even, and some `D i` is odd, i.e. `D i + 1` is even: every vertex would have
odd colour-`i` degree `D i`, so the colour-`i` degree sum `n * D i` would be odd. -/
theorem parity_obstruction (c : V → V → ι) (hsymm : ∀ x y, c x y = c y x) (D : ι → ℕ)
    (hcap : ∀ v i, (nbhd c i v).card ≤ D i)
    (hn : Fintype.card V = ∑ i, D i + 1)
    (heven : Even (∑ i, D i)) (hodd : ∃ i, Odd (D i)) : False := by
  obtain ⟨i, hi⟩ := hodd
  have hsum : ∑ v, (nbhd c i v).card = Fintype.card V * D i := by
    rw [Finset.sum_congr rfl (fun v _ => caps_tight c D hcap hn v i)]
    simp
  have hh := handshake c hsymm i
  rw [hsum] at hh
  have hnodd : Odd (Fintype.card V) := by
    rw [hn]; exact heven.add_one
  exact (Nat.not_even_iff_odd.mpr (Nat.odd_mul.mpr ⟨hnodd, hi⟩)) hh

/-- **Recurrence with parity, counting form.**  Under the caps, if `∑ i, D i` is even and some
`D i` is odd, then `n ≤ ∑ i, D i`, one less than `recurrence_count` allows. -/
theorem recurrence_parity_count (c : V → V → ι) (hsymm : ∀ x y, c x y = c y x) (D : ι → ℕ)
    (hcap : ∀ v i, (nbhd c i v).card ≤ D i)
    (heven : Even (∑ i, D i)) (hodd : ∃ i, Odd (D i)) :
    Fintype.card V ≤ ∑ i, D i := by
  have h1 := recurrence_count c D hcap
  by_contra h
  exact parity_obstruction c hsymm D hcap (by omega) heven hodd

/-- **Paper form of the counting statements**, with `r = Fintype.card ι ≥ 2` colours and
right-hand side `P = ∑ i, (D i + 1) - (r - 2)` (that is, `∑ R(t - e_i) - (r - 2)` with
`R(t - e_i) = D i + 1`):
`n < P`; and if `P` is even and some `D i + 1` is even, then also `n ≠ P - 1`, so `n < P - 1`.
The hypothesis `2 ≤ r` is needed only because `ℕ` subtraction truncates `r - 2`. -/
theorem recurrence_count_paper (c : V → V → ι) (hsymm : ∀ x y, c x y = c y x) (D : ι → ℕ)
    (hr : 2 ≤ Fintype.card ι)
    (hcap : ∀ v i, (nbhd c i v).card ≤ D i) :
    Fintype.card V < ∑ i, (D i + 1) - (Fintype.card ι - 2) ∧
      (Even (∑ i, (D i + 1) - (Fintype.card ι - 2)) → (∃ i, Even (D i + 1)) →
        Fintype.card V < ∑ i, (D i + 1) - (Fintype.card ι - 2) - 1) := by
  have hP : ∑ i, (D i + 1) - (Fintype.card ι - 2) = ∑ i, D i + 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    omega
  rw [hP]
  refine ⟨by have := recurrence_count c D hcap; omega, fun heven hodd => ?_⟩
  have heven' : Even (∑ i, D i) := by
    rcases heven with ⟨k, hk⟩
    exact ⟨k - 1, by omega⟩
  have hodd' : ∃ i, Odd (D i) := by
    obtain ⟨i, hi⟩ := hodd
    exact ⟨i, by
      rcases hi with ⟨k, hk⟩
      exact ⟨k - 1, by omega⟩⟩
  have := recurrence_parity_count c hsymm D hcap heven' hodd'
  omega

end Counting

section Ramsey

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `S` is a colour-`i` clique: every pair of distinct vertices of `S` has colour `i`. -/
def IsMonoClique {V : Type*} (c : V → V → ι) (i : ι) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c x y = i

/-- `c` avoids `t`: every colour-`i` clique has fewer than `t i` vertices. -/
def Avoids {V : Type*} (c : V → V → ι) (t : ι → ℕ) : Prop :=
  ∀ i S, IsMonoClique c i S → S.card < t i

/-- `RamseyBound t B` (that is, `R(t) ≤ B`): every symmetric `ι`-colouring of a complete
graph that avoids `t` has fewer than `B` vertices.  See `ramseyBound_iff_fin` for the
equivalence with the textbook definition. -/
def RamseyBound (t : ι → ℕ) (B : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ι),
    (∀ x y, c x y = c y x) → Avoids c t → Fintype.card V < B

omit [Fintype ι] [DecidableEq ι] in
theorem RamseyBound.mono {t : ι → ℕ} {B B' : ℕ} (h : RamseyBound t B) (hB : B ≤ B') :
    RamseyBound t B' := by
  intro V _ _ c hs ha
  exact lt_of_lt_of_le (h V c hs ha) hB

omit [Fintype ι] [DecidableEq ι] in
/-- The no-exact-size form of avoidance: a clique on at least `t i` vertices contains one on
exactly `t i` vertices. -/
theorem avoids_iff_no_exact {V : Type*} [DecidableEq V] (c : V → V → ι) (t : ι → ℕ) :
    Avoids c t ↔ ∀ i (S : Finset V), S.card = t i → ¬ IsMonoClique c i S := by
  constructor
  · intro h i S hS hc
    have := h i S hc
    omega
  · intro h i S hc
    by_contra hn
    obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
    exact h i T hT (fun x hx y hy hxy => hc x (hTS hx) y (hTS hy) hxy)

omit [Fintype ι] [DecidableEq ι] in
/-- **Bridge to the conventional definition.**  `RamseyBound t B` holds iff every symmetric
`ι`-colouring of the edges of `K_B` (vertex set `Fin B`) has, for some colour `i`, a colour-`i`
clique on exactly `t i` vertices; that is the usual meaning of `R(t) ≤ B`. -/
theorem ramseyBound_iff_fin (t : ι → ℕ) (B : ℕ) :
    RamseyBound t B ↔ ∀ c : Fin B → Fin B → ι, (∀ x y, c x y = c y x) →
      ∃ i, ∃ S : Finset (Fin B), S.card = t i ∧ IsMonoClique c i S := by
  constructor
  · intro h c hs
    by_contra hn
    push_neg at hn
    have ha : Avoids c t := (avoids_iff_no_exact c t).mpr (fun i S hS hc => hn i S hS hc)
    have := h (Fin B) c hs ha
    simp at this
  · intro h V _ _ c hs ha
    by_contra hn
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
      (by simpa using (Nat.le_of_not_gt hn) : Fintype.card (Fin B) ≤ Fintype.card V)
    obtain ⟨i, S, hS, hc⟩ := h (fun x y => c (f x) (f y)) (fun x y => hs _ _)
    have hc' : IsMonoClique c i (S.map f) := by
      intro x hx y hy hxy
      obtain ⟨a, ha', rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨b, hb', rfl⟩ := Finset.mem_map.mp hy
      exact hc a ha' b hb' (fun hab => hxy (by rw [hab]))
    have := ha i _ hc'
    rw [Finset.card_map] at this
    omega

omit [Fintype ι] in
/-- The colouring restricted to the colour-`i` neighbourhood of `v` avoids `t - e_i`:
a colour-`i` clique there extends by `v`, and a colour-`j` clique (`j ≠ i`) is one in `V`. -/
theorem avoids_nbhd {V : Type} [Fintype V] [DecidableEq V] (c : V → V → ι)
    (hs : ∀ x y, c x y = c y x) (t : ι → ℕ) (ha : Avoids c t) (i : ι) (v : V) :
    Avoids (fun x y : ↥(nbhd c i v) => c x y) (Function.update t i (t i - 1)) := by
  intro j S hS
  let S' : Finset V := S.map (Function.Embedding.subtype _)
  have hS'card : S'.card = S.card := Finset.card_map _
  have hS' : IsMonoClique c j S' := by
    intro x hx y hy hxy
    obtain ⟨a, ha', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb', rfl⟩ := Finset.mem_map.mp hy
    exact hS a ha' b hb' (fun hab => hxy (by rw [hab]))
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self]
    have hv : v ∉ S' := by
      intro hv
      obtain ⟨a, _, ha'⟩ := Finset.mem_map.mp hv
      exact (mem_nbhd.mp a.2).1 ha'
    have hmem : ∀ w ∈ S', c v w = j := by
      intro w hw
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hw
      exact (mem_nbhd.mp a.2).2
    have hins : IsMonoClique c j (insert v S') := by
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact absurd rfl hxy
        · exact hmem y hy
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · rw [hs]; exact hmem x hx
        · exact hS' x hx y hy hxy
    have := ha j _ hins
    rw [Finset.card_insert_of_notMem hv] at this
    omega
  · rw [Function.update_of_ne hji]
    have := ha j _ hS'
    omega

omit [Fintype ι] in
/-- The cap `d_i(v) ≤ B i - 1` from `R(t - e_i) ≤ B i`. -/
theorem nbhd_card_le {V : Type} [Fintype V] [DecidableEq V] (c : V → V → ι)
    (hs : ∀ x y, c x y = c y x) (t : ι → ℕ) (ha : Avoids c t) (B : ι → ℕ)
    (hB : ∀ i, RamseyBound (Function.update t i (t i - 1)) (B i)) (v : V) (i : ι) :
    (nbhd c i v).card ≤ B i - 1 := by
  have h := hB i (↥(nbhd c i v)) (fun x y => c x y) (fun x y => hs _ _)
    (avoids_nbhd c hs t ha i v)
  rw [Fintype.card_coe] at h
  omega

/-- **Neighbourhood recurrence (`eq:recurrence`, `r` colours).**  If `R(t - e_i) ≤ B i` for
every colour `i`, then `R(t) ≤ ∑ i, (B i - 1) + 2`, which is `∑ i, B i - (r - 2)` when every
`B i ≥ 1` and `r ≥ 2` (see `ramsey_recurrence_paper`). -/
theorem ramsey_recurrence (t : ι → ℕ) (B : ι → ℕ)
    (hB : ∀ i, RamseyBound (Function.update t i (t i - 1)) (B i)) :
    RamseyBound t (∑ i, (B i - 1) + 2) := by
  intro V _ _ c hs ha
  have := recurrence_count c (fun i => B i - 1) (fun v i => nbhd_card_le c hs t ha B hB v i)
  simp only at this
  omega

/-- **Recurrence with parity.**  If moreover `∑ i, (B i - 1)` is even and some `B i - 1` is
odd, then `R(t) ≤ ∑ i, (B i - 1) + 1`. -/
theorem ramsey_recurrence_parity (t : ι → ℕ) (B : ι → ℕ)
    (hB : ∀ i, RamseyBound (Function.update t i (t i - 1)) (B i))
    (heven : Even (∑ i, (B i - 1))) (hodd : ∃ i, Odd (B i - 1)) :
    RamseyBound t (∑ i, (B i - 1) + 1) := by
  intro V _ _ c hs ha
  have := recurrence_parity_count c hs (fun i => B i - 1)
    (fun v i => nbhd_card_le c hs t ha B hB v i) heven hodd
  simp only at this
  omega

/-- **Paper form.**  With `r = Fintype.card ι ≥ 2` and every `B i ≥ 1`:
`R(t) ≤ ∑ i, B i - (r - 2)`, and `R(t) ≤ ∑ i, B i - (r - 2) - 1` when `∑ i, B i - (r - 2)`
is even and some `B i` is even. -/
theorem ramsey_recurrence_paper (t : ι → ℕ) (B : ι → ℕ)
    (hr : 2 ≤ Fintype.card ι) (hB1 : ∀ i, 1 ≤ B i)
    (hB : ∀ i, RamseyBound (Function.update t i (t i - 1)) (B i)) :
    RamseyBound t (∑ i, B i - (Fintype.card ι - 2)) ∧
      (Even (∑ i, B i - (Fintype.card ι - 2)) → (∃ i, Even (B i)) →
        RamseyBound t (∑ i, B i - (Fintype.card ι - 2) - 1)) := by
  have hsum : ∑ i, B i = ∑ i, (B i - 1) + Fintype.card ι := by
    have : ∀ i ∈ (univ : Finset ι), B i = (B i - 1) + 1 := fun i _ => by
      have := hB1 i; omega
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_one]
  have hP : ∑ i, B i - (Fintype.card ι - 2) = ∑ i, (B i - 1) + 2 := by omega
  rw [hP]
  refine ⟨ramsey_recurrence t B hB, fun heven hodd => ?_⟩
  have heven' : Even (∑ i, (B i - 1)) := by
    rcases heven with ⟨k, hk⟩
    exact ⟨k - 1, by omega⟩
  have hodd' : ∃ i, Odd (B i - 1) := by
    obtain ⟨i, hi⟩ := hodd
    refine ⟨i, ?_⟩
    rcases hi with ⟨k, hk⟩
    have := hB1 i
    exact ⟨k - 1, by omega⟩
  have := ramsey_recurrence_parity t B hB heven' hodd'
  exact this.mono (by omega)

omit [Fintype ι] [DecidableEq ι] in
/-- Renaming the colours: `R(t ∘ σ) ≤ R(t)`, so `R` is symmetric in its arguments. -/
theorem RamseyBound.perm {t : ι → ℕ} {B : ℕ} (h : RamseyBound t B) (σ : Equiv.Perm ι) :
    RamseyBound (t ∘ σ) B := by
  intro V _ _ c hs ha
  refine h V (fun x y => σ (c x y)) (fun x y => by simp only [hs x y]) ?_
  intro j S hS
  have hS' : IsMonoClique c (σ.symm j) S := by
    intro x hx y hy hxy
    rw [← hS x hx y hy hxy, Equiv.symm_apply_apply]
  have := ha (σ.symm j) S hS'
  simpa using this

/-- **Dropping an entry equal to `2`.**  A colouring with no colour-`0` clique on `2`
vertices has no colour-`0` edge, so it is a colouring with one colour fewer:
`R(2, t) ≤ R(t)`. -/
theorem RamseyBound.cons_two {r : ℕ} {t : Fin (r + 1) → ℕ} {B : ℕ} (h : RamseyBound t B) :
    RamseyBound (Fin.cons 2 t : Fin (r + 2) → ℕ) B := by
  intro V _ _ c hs ha
  have hne : ∀ x y, x ≠ y → c x y ≠ 0 := by
    intro x y hxy h0
    have hcl : IsMonoClique c 0 ({x, y} : Finset V) := by
      intro a ha' b hb' hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact absurd rfl hab
      · exact h0
      · rw [hs]; exact h0
      · exact absurd rfl hab
    have := ha 0 _ hcl
    rw [Finset.card_pair hxy] at this
    simp at this
  let c' : V → V → Fin (r + 1) := fun x y => if h0 : c x y = 0 then 0 else (c x y).pred h0
  have hc' : ∀ x y, x ≠ y → (c' x y).succ = c x y := by
    intro x y hxy
    simp only [c', dif_neg (hne x y hxy), Fin.succ_pred]
  refine h V c' (fun x y => by simp only [c', hs x y]) ?_
  intro j S hS
  have hS' : IsMonoClique c j.succ S := by
    intro x hx y hy hxy
    rw [← hc' x y hxy, hS x hx y hy hxy]
  have := ha j.succ S hS'
  simpa using this

/-! ### Corollary `cor:four` -/

/-- **Corollary `cor:four`.**  From `R(3,4,4) ≤ 73` (Theorem `thm:r34five`),
`R(4,4,4) ≤ 198` (Theorem `thm:r444five`) and `R(3,3,3,4) ≤ 149` (from the survey), the
four-colour recurrence gives `R(3,3,4,4) ≤ 442`, `R(3,4,4,4) ≤ 1521` (with parity) and
`R(4,4,4,4) ≤ 6082`. -/
theorem cor_four
    (h344 : RamseyBound (![3, 4, 4] : Fin 3 → ℕ) 73)
    (h444 : RamseyBound (![4, 4, 4] : Fin 3 → ℕ) 198)
    (h3334 : RamseyBound (![3, 3, 3, 4] : Fin 4 → ℕ) 149) :
    RamseyBound (![3, 3, 4, 4] : Fin 4 → ℕ) 442 ∧
      RamseyBound (![3, 4, 4, 4] : Fin 4 → ℕ) 1521 ∧
      RamseyBound (![4, 4, 4, 4] : Fin 4 → ℕ) 6082 := by
  -- the inputs in the positions where the recurrence needs them
  have h2344 : RamseyBound (![2, 3, 4, 4] : Fin 4 → ℕ) 73 := h344.cons_two
  have h2444 : RamseyBound (![2, 4, 4, 4] : Fin 4 → ℕ) 198 := h444.cons_two
  -- first line: 2 * 73 + 2 * 149 - 2 = 442
  have h3344 : RamseyBound (![3, 3, 4, 4] : Fin 4 → ℕ) 442 := by
    have := ramsey_recurrence (![3, 3, 4, 4] : Fin 4 → ℕ) ![73, 73, 149, 149] (by
      intro i
      fin_cases i
      · convert h2344 using 1
        ext j; fin_cases j <;> rfl
      · convert h2344.perm (Equiv.swap 0 1) using 1
        ext j; fin_cases j <;> rfl
      · convert h3334 using 1
        ext j; fin_cases j <;> rfl
      · convert h3334.perm (Equiv.swap 2 3) using 1
        ext j; fin_cases j <;> rfl)
    simpa [Fin.sum_univ_four] using this
  -- second line, with parity: 198 + 3 * 442 - 3 = 1521
  have h3444 : RamseyBound (![3, 4, 4, 4] : Fin 4 → ℕ) 1521 := by
    have := ramsey_recurrence_parity (![3, 4, 4, 4] : Fin 4 → ℕ) ![198, 442, 442, 442] (by
      intro i
      fin_cases i
      · convert h2444 using 1
        ext j; fin_cases j <;> rfl
      · convert h3344 using 1
        ext j; fin_cases j <;> rfl
      · convert h3344.perm (Equiv.swap 1 2) using 1
        ext j; fin_cases j <;> rfl
      · convert h3344.perm (Equiv.swap 1 3) using 1
        ext j; fin_cases j <;> rfl)
      (by simp [Fin.sum_univ_four]; decide)
      ⟨0, by simp; decide⟩
    simpa [Fin.sum_univ_four] using this
  -- third line: 4 * 1521 - 2 = 6082
  have h4444 : RamseyBound (![4, 4, 4, 4] : Fin 4 → ℕ) 6082 := by
    have := ramsey_recurrence (![4, 4, 4, 4] : Fin 4 → ℕ) ![1521, 1521, 1521, 1521] (by
      intro i
      fin_cases i
      · convert h3444 using 1
        ext j; fin_cases j <;> rfl
      · convert h3444.perm (Equiv.swap 0 1) using 1
        ext j; fin_cases j <;> rfl
      · convert h3444.perm (Equiv.swap 0 2) using 1
        ext j; fin_cases j <;> rfl
      · convert h3444.perm (Equiv.swap 0 3) using 1
        ext j; fin_cases j <;> rfl)
    simpa [Fin.sum_univ_four] using this
  exact ⟨h3344, h3444, h4444⟩

/-- The survey's input `R(3,3,3,4) ≤ 149` is itself the recurrence with parity from
`R(3,3,4) ≤ 30` and `R(3,3,3,3) ≤ 62` (paragraph "The inputs and earlier bounds" after
`cor:four`): `3 * 30 + 62 = 152` and `30` are even, giving `152 - 3 = 149`. -/
theorem r3334_le
    (h334 : RamseyBound (![3, 3, 4] : Fin 3 → ℕ) 30)
    (h3333 : RamseyBound (![3, 3, 3, 3] : Fin 4 → ℕ) 62) :
    RamseyBound (![3, 3, 3, 4] : Fin 4 → ℕ) 149 := by
  have h2334 : RamseyBound (![2, 3, 3, 4] : Fin 4 → ℕ) 30 := h334.cons_two
  have := ramsey_recurrence_parity (![3, 3, 3, 4] : Fin 4 → ℕ) ![30, 30, 30, 62] (by
    intro i
    fin_cases i
    · convert h2334 using 1
      ext j; fin_cases j <;> rfl
    · convert h2334.perm (Equiv.swap 0 1) using 1
      ext j; fin_cases j <;> rfl
    · convert h2334.perm (Equiv.swap 0 2) using 1
      ext j; fin_cases j <;> rfl
    · convert h3333 using 1
      ext j; fin_cases j <;> rfl)
    (by simp [Fin.sum_univ_four]; decide)
    ⟨0, by simp; decide⟩
  simpa [Fin.sum_univ_four] using this

/-- `cor:four` with `R(3,3,3,4) ≤ 149` replaced by its own inputs `R(3,3,4) ≤ 30` and
`R(3,3,3,3) ≤ 62`. -/
theorem cor_four_from_r334
    (h344 : RamseyBound (![3, 4, 4] : Fin 3 → ℕ) 73)
    (h444 : RamseyBound (![4, 4, 4] : Fin 3 → ℕ) 198)
    (h334 : RamseyBound (![3, 3, 4] : Fin 3 → ℕ) 30)
    (h3333 : RamseyBound (![3, 3, 3, 3] : Fin 4 → ℕ) 62) :
    RamseyBound (![3, 3, 4, 4] : Fin 4 → ℕ) 442 ∧
      RamseyBound (![3, 4, 4, 4] : Fin 4 → ℕ) 1521 ∧
      RamseyBound (![4, 4, 4, 4] : Fin 4 → ℕ) 6082 :=
  cor_four h344 h444 (r3334_le h334 h3333)

/-! ### Sanity checks and the Introduction's worked parity example

These use no Ramsey hypotheses except where stated, and show the predicate `RamseyBound`
reproduces classical values through the recurrence. -/

/-- One colour: a colouring of `K_n` in one colour with no `K_3` has `n < 3`. -/
theorem r3_one_colour : RamseyBound (![3] : Fin 1 → ℕ) 3 := by
  intro V _ _ c _ ha
  have hcl : IsMonoClique c 0 (univ : Finset V) :=
    fun x _ y _ _ => Subsingleton.elim _ _
  simpa using ha 0 univ hcl

/-- `R(3,3) ≤ 6` from the recurrence `R(2,3) + R(3,2) = 3 + 3`. -/
theorem r33_le_six : RamseyBound (![3, 3] : Fin 2 → ℕ) 6 := by
  have h23 : RamseyBound (![2, 3] : Fin 2 → ℕ) 3 := r3_one_colour.cons_two
  have := ramsey_recurrence (![3, 3] : Fin 2 → ℕ) ![3, 3] (by
    intro i
    fin_cases i
    · convert h23 using 1
      ext j; fin_cases j <;> rfl
    · convert h23.perm (Equiv.swap 0 1) using 1
      ext j; fin_cases j <;> rfl)
  simpa [Fin.sum_univ_two] using this

/-- `R(3,3,3) ≤ 17` (Greenwood and Gleason) from the recurrence `3 * 6 - 1`. -/
theorem r333_le_17 : RamseyBound (![3, 3, 3] : Fin 3 → ℕ) 17 := by
  have h233 : RamseyBound (![2, 3, 3] : Fin 3 → ℕ) 6 := r33_le_six.cons_two
  have := ramsey_recurrence (![3, 3, 3] : Fin 3 → ℕ) ![6, 6, 6] (by
    intro i
    fin_cases i
    · convert h233 using 1
      ext j; fin_cases j <;> rfl
    · convert h233.perm (Equiv.swap 0 1) using 1
      ext j; fin_cases j <;> rfl
    · convert h233.perm (Equiv.swap 0 2) using 1
      ext j; fin_cases j <;> rfl)
  simpa [Fin.sum_univ_three] using this

/-- The Introduction's example of the parity refinement: `R(3,3,6) ≤ 91` from `R(3,6) ≤ 18`
and `R(3,3,5) ≤ 57`; the right-hand side `18 + 18 + 57 - 1 = 92` and `18` are even. -/
theorem r336_le
    (h36 : RamseyBound (![3, 6] : Fin 2 → ℕ) 18)
    (h335 : RamseyBound (![3, 3, 5] : Fin 3 → ℕ) 57) :
    RamseyBound (![3, 3, 6] : Fin 3 → ℕ) 91 := by
  have h236 : RamseyBound (![2, 3, 6] : Fin 3 → ℕ) 18 := h36.cons_two
  have := ramsey_recurrence_parity (![3, 3, 6] : Fin 3 → ℕ) ![18, 18, 57] (by
    intro i
    fin_cases i
    · convert h236 using 1
      ext j; fin_cases j <;> rfl
    · convert h236.perm (Equiv.swap 0 1) using 1
      ext j; fin_cases j <;> rfl
    · convert h335 using 1
      ext j; fin_cases j <;> rfl)
    (by simp [Fin.sum_univ_three]; decide)
    ⟨0, by simp; decide⟩
  simpa [Fin.sum_univ_three] using this

end Ramsey

end RamseyLean.Recurrence

#print axioms RamseyLean.Recurrence.recurrence_count
#print axioms RamseyLean.Recurrence.handshake
#print axioms RamseyLean.Recurrence.parity_obstruction
#print axioms RamseyLean.Recurrence.recurrence_parity_count
#print axioms RamseyLean.Recurrence.recurrence_count_paper
#print axioms RamseyLean.Recurrence.ramseyBound_iff_fin
#print axioms RamseyLean.Recurrence.ramsey_recurrence
#print axioms RamseyLean.Recurrence.ramsey_recurrence_parity
#print axioms RamseyLean.Recurrence.ramsey_recurrence_paper
#print axioms RamseyLean.Recurrence.RamseyBound.perm
#print axioms RamseyLean.Recurrence.RamseyBound.cons_two
#print axioms RamseyLean.Recurrence.cor_four
#print axioms RamseyLean.Recurrence.r3334_le
#print axioms RamseyLean.Recurrence.cor_four_from_r334
#print axioms RamseyLean.Recurrence.r33_le_six
#print axioms RamseyLean.Recurrence.r333_le_17
#print axioms RamseyLean.Recurrence.r336_le
