import RamseyLean.LocalCombinatorics
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Nat.Choose.Basic

/-!
# Three short lemmas of the paper: `lem:cert`, `lem:delete`, `lem:line`

Paper: `paper/neighbourhood_counting.tex` (labels cited, not line numbers).

* `lem:cert` (Section "Extending a split circulant"): certifiers bound the
  green cliques of `H - A_S`.  Formalised as `RamseyLean.Lemmas.lem_cert_core`,
  `RamseyLean.Lemmas.lem_cert`, together with the decomposition of green cliques of
  the extension and the criterion stated right after the lemma
  (`RamseyLean.Lemmas.greenClique_card_le_of_certifiers`).
* `lem:delete` (Section "Merging two triangle-free colours"): valid lower
  bounds pass to larger orders, by deleting a vertex (`lem_delete_a`) and by
  averaging over `s`-subsets (`lem_delete_b`).
* `lem:line`: a line below `f` at the admissible degrees gives a valid lower
  bound (`lem_line_a`), and `f > 0` at the admissible degrees excludes the
  order (`lem_line_b`).

Conventions.  A colouring is a function `c : V → V → Colour`; a colouring of
`E(K_n)` is a symmetric one, used on an `n`-element vertex set `S : Finset V`
(of an arbitrary type `V`).  The diagonal is never used.  Ramsey numbers enter
only through explicit hypotheses `Bound33 k B` ("every vertex set on which the
colouring has no red triangle, no blue triangle and no green `K_k` has fewer
than `B` vertices", which is what `R(3,3,k) ≤ B` gives) and `BoundRB k B`
("... no red edge, no blue triangle and no green `K_k` ...", which is what
`R(3,k) = R(2,3,k) ≤ B` gives).  Bridge lemmas at the end derive them from the
conventional definition of `R(t₁,t₂,t₃) ≤ B` on colourings of `K_B`.
-/

namespace RamseyLean.Lemmas

open RamseyLocal Finset
open RamseyLocal.Colour

/-! ## Colours -/

theorem colour_eq_green_of_not_red_blue {a : Colour} (h : ¬ (a = red ∨ a = blue)) :
    a = green := by
  cases a <;> simp_all

theorem colour_ne_green_iff (a : Colour) : a ≠ green ↔ (a = red ∨ a = blue) := by
  cases a <;> simp

/-! ## Part 1: `lem:cert` -/

section Cert

variable {V : Type*} [DecidableEq V]

/-- `w` *certifies* the attachment set `A` (in the paper `A = A_S`): `w` and all
its red and blue neighbours in `H` lie in `A`. -/
def Certifies (c : V → V → Colour) (A : Finset V) (w : V) : Prop :=
  w ∈ A ∧ ∀ u, u ≠ w → (c w u = red ∨ c w u = blue) → u ∈ A

/-- **Lemma `lem:cert`, core form.**  Let `H` (colouring `c`) have every green
clique of size at most `q`.  If `W` is a set of certifiers of `A` that is a
green clique, then every green clique `T` of `H - A` satisfies
`|T| + |W| ≤ q`. -/
theorem lem_cert_core (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x) (q : ℕ)
    (hq : ∀ T : Finset V, GreenClique c T → T.card ≤ q)
    (A W : Finset V) (hW : ∀ w ∈ W, Certifies c A w) (hWg : GreenClique c W)
    (T : Finset V) (hTA : ∀ t ∈ T, t ∉ A) (hTg : GreenClique c T) :
    T.card + W.card ≤ q := by
  -- `T` is disjoint from `W`, as `W ⊆ A`.
  have hdisj : Disjoint T W := by
    rw [Finset.disjoint_left]
    intro t ht htW
    exact hTA t ht (hW t htW).1
  -- a vertex of `T` is green to every `w ∈ W`
  have hcross : ∀ t ∈ T, ∀ w ∈ W, c w t = green := by
    intro t ht w hw
    apply colour_eq_green_of_not_red_blue
    intro hrb
    have htw : t ≠ w := fun h => hTA t ht (h ▸ (hW w hw).1)
    exact hTA t ht ((hW w hw).2 t htw hrb)
  have hclique : GreenClique c (T ∪ W) := by
    intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hxT | hxW <;>
      rcases Finset.mem_union.mp hy with hyT | hyW
    · exact hTg x hxT y hyT hxy
    · rw [hsymm]; exact hcross x hxT y hyW
    · exact hcross y hyT x hxW
    · exact hWg x hxW y hyW hxy
  have := hq _ hclique
  rwa [Finset.card_union_of_disjoint hdisj] at this

/-- `lem:cert` in the paper's form `|T| ≤ q - |W|`. -/
theorem lem_cert_core' (c : V → V → Colour) (hsymm : ∀ x y, c x y = c y x) (q : ℕ)
    (hq : ∀ T : Finset V, GreenClique c T → T.card ≤ q)
    (A W : Finset V) (hW : ∀ w ∈ W, Certifies c A w) (hWg : GreenClique c W)
    (T : Finset V) (hTA : ∀ t ∈ T, t ∉ A) (hTg : GreenClique c T) :
    T.card ≤ q - W.card := by
  have := lem_cert_core c hsymm q hq A W hW hWg T hTA hTg
  omega

/-! ### The extension `F` of `H` by new vertices

The vertices of `F` are `V ⊕ N`: `Sum.inl v` is the vertex `v` of `H`,
`Sum.inr x` is a new vertex `x`. -/

variable {N : Type*}

/-- The colouring `H`: the restriction of `F` to the old vertices. -/
def oldPart (F : V ⊕ N → V ⊕ N → Colour) : V → V → Colour :=
  fun u v => F (Sum.inl u) (Sum.inl v)

/-- The colouring of `F` among the new vertices. -/
def newPart (F : V ⊕ N → V ⊕ N → Colour) : N → N → Colour :=
  fun x y => F (Sum.inr x) (Sum.inr y)

variable [Fintype V]

/-- `A_x`: the vertices of `H` joined to the new vertex `x` in red or blue. -/
def attach (F : V ⊕ N → V ⊕ N → Colour) (x : N) : Finset V :=
  Finset.univ.filter fun v => F (Sum.inr x) (Sum.inl v) = red ∨ F (Sum.inr x) (Sum.inl v) = blue

/-- `A_S = ⋃_{x ∈ S} A_x`. -/
def attachSet (F : V ⊕ N → V ⊕ N → Colour) (S : Finset N) : Finset V :=
  S.biUnion (attach F)

/-- **Lemma `lem:cert`** in the setting of the paper: `H = oldPart F`, `S` a set
of new vertices, `W` a set of certifiers of `S` that is a green clique of `H`.
Every green clique `T` of `H - A_S` has at most `q - |W|` vertices. -/
theorem lem_cert (F : V ⊕ N → V ⊕ N → Colour) (hsymm : ∀ a b, F a b = F b a) (q : ℕ)
    (hq : ∀ T : Finset V, GreenClique (oldPart F) T → T.card ≤ q)
    (S : Finset N) (W : Finset V)
    (hW : ∀ w ∈ W, Certifies (oldPart F) (attachSet F S) w)
    (hWg : GreenClique (oldPart F) W)
    (T : Finset V) (hTA : ∀ t ∈ T, t ∉ attachSet F S) (hTg : GreenClique (oldPart F) T) :
    T.card ≤ q - W.card :=
  lem_cert_core' (oldPart F) (fun _ _ => hsymm _ _) q hq (attachSet F S) W hW hWg T hTA hTg

/-- The decomposition before `lem:cert`: every green clique `K` of `F` is
`S ∪ T`, where `S` (its set of new vertices) is a green clique and `T` (its
set of old vertices) is a green clique of `H - A_S`. -/
theorem greenClique_decomp (F : V ⊕ N → V ⊕ N → Colour) (K : Finset (V ⊕ N))
    (hK : GreenClique F K) :
    GreenClique (newPart F) K.toRight ∧ GreenClique (oldPart F) K.toLeft ∧
      (∀ t ∈ K.toLeft, t ∉ attachSet F K.toRight) ∧
      K.card = K.toRight.card + K.toLeft.card := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hK _ (Finset.mem_toRight.mp hx) _ (Finset.mem_toRight.mp hy)
      (fun h => hxy (Sum.inr_injective h))
  · intro x hx y hy hxy
    exact hK _ (Finset.mem_toLeft.mp hx) _ (Finset.mem_toLeft.mp hy)
      (fun h => hxy (Sum.inl_injective h))
  · intro t ht htA
    obtain ⟨x, hx, htx⟩ := Finset.mem_biUnion.mp htA
    have hg : F (Sum.inr x) (Sum.inl t) = green :=
      hK _ (Finset.mem_toRight.mp hx) _ (Finset.mem_toLeft.mp ht) (by simp)
    have := (Finset.mem_filter.mp htx).2
    rw [hg] at this
    simp at this
  · rw [← Finset.card_toLeft_add_card_toRight (u := K)]
    omega

/-- The criterion stated after `lem:cert`: if every green clique `S` of new
vertices has a green clique `W` of certifiers (of `A_S`) in `H` with
`|S| ≤ 1 + |W|` (that is, `|S| ≤ 1 + ω(W_S)`), then `F` has green clique number
at most `q + 1`. -/
theorem greenClique_card_le_of_certifiers (F : V ⊕ N → V ⊕ N → Colour)
    (hsymm : ∀ a b, F a b = F b a) (q : ℕ)
    (hq : ∀ T : Finset V, GreenClique (oldPart F) T → T.card ≤ q)
    (hcrit : ∀ S : Finset N, GreenClique (newPart F) S →
      ∃ W : Finset V, (∀ w ∈ W, Certifies (oldPart F) (attachSet F S) w) ∧
        GreenClique (oldPart F) W ∧ S.card ≤ 1 + W.card)
    (K : Finset (V ⊕ N)) (hK : GreenClique F K) : K.card ≤ q + 1 := by
  obtain ⟨hS, hT, hTA, hcard⟩ := greenClique_decomp F K hK
  obtain ⟨W, hW, hWg, hSW⟩ := hcrit _ hS
  have := lem_cert_core (oldPart F) (fun _ _ => hsymm _ _) q hq (attachSet F K.toRight) W hW hWg
    K.toLeft hTA hT
  omega

end Cert

/-! ## Part 2: colourings of vertex sets and edge counting -/

section Colourings

variable {V : Type*} [DecidableEq V]

/-- `c` is symmetric, i.e. a colouring of the edges of a complete graph. -/
def Symm (c : V → V → Colour) : Prop := ∀ x y, c x y = c y x

/-- No triangle of colour `a` on three distinct vertices of `S`. -/
def NoMonoTri (c : V → V → Colour) (a : Colour) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → x ≠ z → y ≠ z →
    c x y = a → c x z = a → c y z = a → False

/-- No edge of colour `a` inside `S` (no `K_2` of colour `a`). -/
def NoColourEdge (c : V → V → Colour) (a : Colour) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c x y ≠ a

/-- No green `K_k` inside `S`: every green clique in `S` has fewer than `k`
vertices (see `noGreenK_iff` for the literal form). -/
def NoGreenK (c : V → V → Colour) (k : ℕ) (S : Finset V) : Prop :=
  ∀ T ⊆ S, GreenClique c T → T.card < k

/-- The colouring `c` on `S` is a `(3,3,k)`-colouring: no red or blue triangle
and no green `K_k`. -/
def Is33k (c : V → V → Colour) (k : ℕ) (S : Finset V) : Prop :=
  NoMonoTri c red S ∧ NoMonoTri c blue S ∧ NoGreenK c k S

omit [DecidableEq V] in
theorem noGreenK_iff (c : V → V → Colour) (k : ℕ) (S : Finset V) :
    NoGreenK c k S ↔ ∀ T ⊆ S, T.card = k → ¬ GreenClique c T := by
  constructor
  · intro h T hTS hcard hT
    have := h T hTS hT
    omega
  · intro h T hTS hT
    by_contra hn
    obtain ⟨U, hUT, hU⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
    exact h U (hUT.trans hTS) hU (fun x hx y hy hxy => hT x (hUT hx) y (hUT hy) hxy)

omit [DecidableEq V] in
/-- Restriction to fewer vertices preserves being a `(3,3,k)`-colouring. -/
theorem Is33k.mono {c : V → V → Colour} {k : ℕ} {S T : Finset V} (h : Is33k c k S)
    (hTS : T ⊆ S) : Is33k c k T :=
  ⟨fun x hx y hy z hz => h.1 x (hTS hx) y (hTS hy) z (hTS hz),
   fun x hx y hy z hz => h.2.1 x (hTS hx) y (hTS hy) z (hTS hz),
   fun U hU => h.2.2 U (hU.trans hTS)⟩

/-! ### Abstract edge counting for a symmetric relation -/

section Counting

variable (adj : V → V → Prop) [DecidableRel adj]

/-- Degree of `v` inside `S`. -/
def deg (S : Finset V) (v : V) : ℕ := (S.filter fun u => u ≠ v ∧ adj v u).card

/-- The edges inside `S`, as two-element subsets. -/
def edgesIn (S : Finset V) : Finset (Finset V) :=
  (S.powersetCard 2).filter fun e => ∀ x ∈ e, ∀ y ∈ e, x ≠ y → adj x y

/-- `e(S)`: the number of edges inside `S`. -/
def ecount (S : Finset V) : ℕ := (edgesIn adj S).card

/-- Ordered count: the number of ordered pairs of distinct adjacent vertices of `S`. -/
def ocount (S : Finset V) : ℕ := ∑ x ∈ S, ∑ y ∈ S, if y ≠ x ∧ adj x y then 1 else 0

theorem deg_eq_sum (S : Finset V) (v : V) :
    deg adj S v = ∑ u ∈ S, if u ≠ v ∧ adj v u then 1 else 0 := by
  unfold deg; rw [Finset.card_filter]

theorem ocount_eq_sum_deg (S : Finset V) : ocount adj S = ∑ v ∈ S, deg adj S v := by
  unfold ocount; simp_rw [deg_eq_sum]

variable {adj}

/-- Handshake lemma: twice the number of edges is the ordered count. -/
theorem ocount_eq_two_mul_ecount (hs : ∀ x y, adj x y → adj y x) (S : Finset V) :
    ocount adj S = 2 * ecount adj S := by
  classical
  set P : Finset (V × V) := (S ×ˢ S).filter fun p => p.2 ≠ p.1 ∧ adj p.1 p.2 with hP
  have hO : ocount adj S = P.card := by
    rw [hP, Finset.card_filter, Finset.sum_product]
    rfl
  have hmaps : Set.MapsTo (fun p : V × V => ({p.1, p.2} : Finset V)) P (edgesIn adj S) := by
    intro p hp
    simp only [hP, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp
    obtain ⟨⟨h1, h2⟩, hne, hadj⟩ := hp
    simp only [edgesIn, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powersetCard]
    refine ⟨⟨?_, Finset.card_pair (Ne.symm hne)⟩, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact h1
      · rw [Finset.mem_singleton.mp hz]; exact h2
    · intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hadj
      · exact hs _ _ hadj
      · exact absurd rfl hxy
  rw [hO, Finset.card_eq_sum_card_fiberwise hmaps, ecount, mul_comm]
  apply Finset.sum_const_nat
  intro e he
  simp only [edgesIn, Finset.mem_filter, Finset.mem_powersetCard] at he
  obtain ⟨⟨heS, hcard⟩, hadje⟩ := he
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have hfib : P.filter (fun p => ({p.1, p.2} : Finset V) = {a, b}) = {(a, b), (b, a)} := by
    ext ⟨x, y⟩
    simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hx, hy⟩, hne, _⟩, hxy⟩
      have hxm : x ∈ ({a, b} : Finset V) := hxy ▸ Finset.mem_insert_self x {y}
      have hym : y ∈ ({a, b} : Finset V) := hxy ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxm hym
      rcases hxm with rfl | rfl <;> rcases hym with rfl | rfl
      · exact absurd rfl hne
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hne
    · have haS : a ∈ S := heS (by simp)
      have hbS : b ∈ S := heS (by simp)
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨⟨haS, hbS⟩, Ne.symm hab, hadje x (by simp) y (by simp) hab⟩, rfl⟩
      · exact ⟨⟨⟨hbS, haS⟩, hab, hadje x (by simp) y (by simp) (Ne.symm hab)⟩,
          Finset.pair_comm _ _⟩
  rw [hfib, Finset.card_pair]
  intro h
  simp only [Prod.mk.injEq] at h
  exact hab h.1

/-- Deleting a vertex: `O(S) = O(S - v) + 2 deg_S(v)`. -/
theorem ocount_erase (hs : ∀ x y, adj x y → adj y x) {S : Finset V} {v : V} (hv : v ∈ S) :
    ocount adj S = ocount adj (S.erase v) + 2 * deg adj S v := by
  set S' := S.erase v
  have hvS' : v ∉ S' := Finset.notMem_erase v S
  have hS : S = insert v S' := (Finset.insert_erase hv).symm
  have hsymm : ∀ x, (if v ≠ x ∧ adj x v then 1 else 0) = (if x ≠ v ∧ adj v x then 1 else 0) := by
    intro x
    by_cases hx : x = v
    · simp [hx]
    · have : adj x v ↔ adj v x := ⟨hs _ _, hs _ _⟩
      simp [hx, Ne.symm hx, this]
  rw [deg_eq_sum, hS, ocount, Finset.sum_insert hvS', Finset.sum_insert hvS']
  simp_rw [Finset.sum_insert hvS']
  rw [Finset.sum_add_distrib]
  simp only [ne_eq, not_true_eq_false, false_and, if_false, zero_add]
  simp_rw [hsymm]
  unfold ocount
  ring

/-- Deleting a vertex: `e(S) = e(S - v) + deg_S(v)`. -/
theorem ecount_erase (hs : ∀ x y, adj x y → adj y x) {S : Finset V} {v : V} (hv : v ∈ S) :
    ecount adj S = ecount adj (S.erase v) + deg adj S v := by
  have := ocount_erase hs hv
  rw [ocount_eq_two_mul_ecount hs, ocount_eq_two_mul_ecount hs] at this
  omega

/-- The number of `s`-subsets of `S` containing two given distinct vertices of `S`
is `binom(|S|-2, s-2)`. -/
theorem card_powersetCard_filter_pair {S : Finset V} {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x ≠ y) {s : ℕ} (hs : 2 ≤ s) :
    ((S.powersetCard s).filter fun T => x ∈ T ∧ y ∈ T).card = (S.card - 2).choose (s - 2) := by
  have hyx : y ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
  have hS'' : ((S.erase x).erase y).card = S.card - 2 := by
    rw [Finset.card_erase_of_mem hyx, Finset.card_erase_of_mem hx]
    omega
  rw [← hS'', ← Finset.card_powersetCard]
  apply Finset.card_nbij' (fun T => (T.erase x).erase y) (fun U => insert x (insert y U))
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hT
    obtain ⟨⟨hTS, hTc⟩, hxT, hyT⟩ := hT
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.erase_subset_erase _ (Finset.erase_subset_erase _ hTS), ?_⟩
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hxy, hyT⟩),
      Finset.card_erase_of_mem hxT, hTc]
    omega
  · intro U hU
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hU
    obtain ⟨hUS, hUc⟩ := hU
    have hyU : y ∉ U := fun h => Finset.notMem_erase y _ (hUS h)
    have hxU : x ∉ U := fun h =>
      Finset.notMem_erase x S (Finset.mem_of_mem_erase (hUS h))
    have hxyU : x ∉ insert y U := by
      rw [Finset.mem_insert]; rintro (h | h)
      · exact hxy h
      · exact hxU h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
    · refine Finset.insert_subset hx (Finset.insert_subset hy ?_)
      exact hUS.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
    · rw [Finset.card_insert_of_notMem hxyU, Finset.card_insert_of_notMem hyU, hUc]
      omega
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_filter] at hT
    obtain ⟨_, hxT, hyT⟩ := hT
    simp only
    rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨Ne.symm hxy, hyT⟩), Finset.insert_erase hxT]
  · intro U hU
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hU
    have hyU : y ∉ U := fun h => Finset.notMem_erase y _ (hU.1 h)
    have hxU : x ∉ U := fun h =>
      Finset.notMem_erase x S (Finset.mem_of_mem_erase (hU.1 h))
    have hxyU : x ∉ insert y U := by
      rw [Finset.mem_insert]; rintro (h | h)
      · exact hxy h
      · exact hxU h
    simp only
    rw [Finset.erase_insert hxyU, Finset.erase_insert hyU]

/-- Double counting over `s`-subsets: `∑_{|T| = s} O(T) = binom(|S|-2, s-2) O(S)`. -/
theorem sum_ocount_powersetCard (S : Finset V) {s : ℕ} (hs2 : 2 ≤ s) :
    ∑ T ∈ S.powersetCard s, ocount adj T = (S.card - 2).choose (s - 2) * ocount adj S := by
  have h1 : ∀ T : Finset V,
      ocount adj T = ∑ p ∈ T ×ˢ T, (if p.2 ≠ p.1 ∧ adj p.1 p.2 then 1 else 0) := by
    intro T; rw [ocount, Finset.sum_product]
  simp_rw [h1]
  rw [Finset.sum_comm' (t' := S ×ˢ S)
    (s' := fun p => (S.powersetCard s).filter fun T => p.1 ∈ T ∧ p.2 ∈ T)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    rintro ⟨x, y⟩ hp
    rw [Finset.mem_product] at hp
    rw [Finset.sum_const, smul_eq_mul]
    by_cases hJ : y ≠ x ∧ adj x y
    · simp only [hJ, ne_eq, not_false_eq_true, and_self, if_true, mul_one]
      exact card_powersetCard_filter_pair hp.1 hp.2 (Ne.symm hJ.1) hs2
    · simp only [hJ, if_false, mul_zero]
  · rintro T ⟨x, y⟩
    simp only [Finset.mem_powersetCard, Finset.mem_product, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hTS, hTc⟩, hx, hy⟩
      exact ⟨⟨⟨hTS, hTc⟩, hx, hy⟩, hTS hx, hTS hy⟩
    · rintro ⟨⟨⟨hTS, hTc⟩, hx, hy⟩, _⟩
      exact ⟨⟨hTS, hTc⟩, hx, hy⟩

/-- Double counting over `s`-subsets: `∑_{|T| = s} e(T) = binom(|S|-2, s-2) e(S)`
(each edge lies in `binom(|S|-2, s-2)` of the `s`-subsets). -/
theorem sum_ecount_powersetCard (hs : ∀ x y, adj x y → adj y x) (S : Finset V) {s : ℕ}
    (hs2 : 2 ≤ s) :
    ∑ T ∈ S.powersetCard s, ecount adj T = (S.card - 2).choose (s - 2) * ecount adj S := by
  have h := sum_ocount_powersetCard (adj := adj) S hs2
  simp_rw [ocount_eq_two_mul_ecount hs] at h
  rw [← Finset.mul_sum] at h
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
  rw [h]; ring

end Counting

/-- `n.choose s * (s (s - 1)) = n (n - 1) * (n - 2).choose (s - 2)` for `2 ≤ s ≤ n`, i.e.
`binom(n,s) / binom(n-2,s-2) = n(n-1)/(s(s-1))`. -/
theorem choose_mul_two (n s : ℕ) (hs : 2 ≤ s) (hsn : s ≤ n) :
    n.choose s * (s * (s - 1)) = n * (n - 1) * (n - 2).choose (s - 2) := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 + 1 := ⟨s - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 + 1 := ⟨n - 2, by omega⟩
  rw [show s' + 1 + 1 - 1 = s' + 1 by omega, show s' + 1 + 1 - 2 = s' by omega,
    show n' + 1 + 1 - 1 = n' + 1 by omega, show n' + 1 + 1 - 2 = n' by omega]
  have h1 := Nat.succ_mul_choose_eq (n' + 1) (s' + 1)
  have h2 := Nat.succ_mul_choose_eq n' s'
  simp only [Nat.succ_eq_add_one] at h1 h2
  calc (n' + 1 + 1).choose (s' + 1 + 1) * ((s' + 1 + 1) * (s' + 1))
      = ((n' + 1 + 1).choose (s' + 1 + 1) * (s' + 1 + 1)) * (s' + 1) := by ring
    _ = ((n' + 1 + 1) * (n' + 1).choose (s' + 1)) * (s' + 1) := by rw [h1]
    _ = (n' + 1 + 1) * ((n' + 1).choose (s' + 1) * (s' + 1)) := by ring
    _ = (n' + 1 + 1) * ((n' + 1) * n'.choose s') := by rw [h2]
    _ = (n' + 1 + 1) * (n' + 1) * n'.choose s' := by ring

/-! ### The red-or-blue graph `H` of a colouring -/

/-- `h_v`: the degree of `v` in the red-or-blue graph `H` of `c` on `S`. -/
def hdeg (c : V → V → Colour) (S : Finset V) (v : V) : ℕ := deg (fun x y => c x y ≠ green) S v

/-- `d_a(v)` on `S`: the number of `u ∈ S`, `u ≠ v`, with `c v u = a`.  The green
degree `z_v` is `colourDeg c green S v`. -/
def colourDeg (c : V → V → Colour) (a : Colour) (S : Finset V) (v : V) : ℕ :=
  (S.filter fun u => u ≠ v ∧ c v u = a).card

/-- `e(H)` on `S`: the number of red or blue edges (2-subsets) inside `S`. -/
def eH (c : V → V → Colour) (S : Finset V) : ℕ := ecount (fun x y => c x y ≠ green) S

omit [DecidableEq V] in
theorem nongreen_symm {c : V → V → Colour} (hc : Symm c) :
    ∀ x y, c x y ≠ green → c y x ≠ green := by
  intro x y h; rwa [← hc x y]

/-- `∑_v h_v = 2 e(H)`. -/
theorem sum_hdeg {c : V → V → Colour} (hc : Symm c) (S : Finset V) :
    ∑ v ∈ S, hdeg c S v = 2 * eH c S := by
  rw [eH, ← ocount_eq_two_mul_ecount (nongreen_symm hc), ocount_eq_sum_deg]
  rfl

/-- `e(H) = e(H - v) + h_v`. -/
theorem eH_erase {c : V → V → Colour} (hc : Symm c) {S : Finset V} {v : V} (hv : v ∈ S) :
    eH c S = eH c (S.erase v) + hdeg c S v :=
  ecount_erase (nongreen_symm hc) hv

/-- `h_v + z_v = |S| - 1`. -/
theorem hdeg_add_greenDeg (c : V → V → Colour) {S : Finset V} {v : V} (hv : v ∈ S) :
    hdeg c S v + colourDeg c green S v + 1 = S.card := by
  have h1 : S.filter (fun u => u ≠ v ∧ c v u ≠ green) =
      (S.erase v).filter (fun u => c v u ≠ green) := by
    ext u; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  have h2 : S.filter (fun u => u ≠ v ∧ c v u = green) =
      (S.erase v).filter (fun u => ¬ (c v u ≠ green)) := by
    ext u; simp only [Finset.mem_filter, Finset.mem_erase, not_not]; tauto
  unfold hdeg deg colourDeg
  rw [h1, h2, Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_erase_of_mem hv]
  have : 1 ≤ S.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

/-- `h_v = d_1(v) + d_2(v)`. -/
theorem hdeg_eq_red_add_blue (c : V → V → Colour) (S : Finset V) (v : V) :
    hdeg c S v = colourDeg c red S v + colourDeg c blue S v := by
  unfold hdeg deg colourDeg
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_union]
    cases hcv : c v u <;> simp
  · rw [Finset.disjoint_filter]
    intro u _ h1 h2
    rw [h1.2] at h2
    exact absurd h2.2 (by simp)

/-- The green neighbourhood `N_3(v)` of a `(3,3,k)`-colouring carries a
`(3,3,k-1)`-colouring (a green `K_{k-1}` there would extend by `v`). -/
theorem greenNbhd_is33 {c : V → V → Colour} (hc : Symm c) {k : ℕ} {S : Finset V}
    (hS : Is33k c k S) {v : V} (hv : v ∈ S) :
    Is33k c (k - 1) (S.filter fun u => u ≠ v ∧ c v u = green) := by
  have hsub : (S.filter fun u => u ≠ v ∧ c v u = green) ⊆ S := Finset.filter_subset _ _
  refine ⟨(hS.mono hsub).1, (hS.mono hsub).2.1, ?_⟩
  intro T hT hTg
  have hvT : v ∉ T := fun h => (Finset.mem_filter.mp (hT h)).2.1 rfl
  have hins : insert v T ⊆ S := Finset.insert_subset hv (hT.trans hsub)
  have hg : GreenClique c (insert v T) := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with hxv | hxT <;>
      rcases Finset.mem_insert.mp hy with hyv | hyT
    · exact absurd (hxv.trans hyv.symm) hxy
    · rw [hxv]; exact (Finset.mem_filter.mp (hT hyT)).2.2
    · rw [hyv, hc]; exact (Finset.mem_filter.mp (hT hxT)).2.2
    · exact hTg x hxT y hyT hxy
  have := hS.2.2 _ hins hg
  rw [Finset.card_insert_of_notMem hvT] at this
  omega

/-- The red neighbourhood `N_1(v)` of a `(3,3,k)`-colouring has no red edge, no
blue triangle and no green `K_k`. -/
theorem redNbhd_props {c : V → V → Colour} {k : ℕ} {S : Finset V} (hS : Is33k c k S)
    {v : V} (hv : v ∈ S) :
    NoColourEdge c red (S.filter fun u => u ≠ v ∧ c v u = red) ∧
      NoMonoTri c blue (S.filter fun u => u ≠ v ∧ c v u = red) ∧
      NoGreenK c k (S.filter fun u => u ≠ v ∧ c v u = red) := by
  have hsub : (S.filter fun u => u ≠ v ∧ c v u = red) ⊆ S := Finset.filter_subset _ _
  refine ⟨?_, (hS.mono hsub).2.1, (hS.mono hsub).2.2⟩
  intro x hx y hy hxy hcxy
  rw [Finset.mem_filter] at hx hy
  exact hS.1 v hv x hx.1 y hy.1 (Ne.symm hx.2.1) (Ne.symm hy.2.1) hxy hx.2.2 hy.2.2 hcxy

/-- Interchanging red and blue. -/
def swapRB : Colour → Colour
  | red => blue
  | blue => red
  | green => green

@[simp] theorem swapRB_eq_red (a : Colour) : swapRB a = red ↔ a = blue := by
  cases a <;> simp [swapRB]

@[simp] theorem swapRB_eq_blue (a : Colour) : swapRB a = blue ↔ a = red := by
  cases a <;> simp [swapRB]

@[simp] theorem swapRB_eq_green (a : Colour) : swapRB a = green ↔ a = green := by
  cases a <;> simp [swapRB]

omit [DecidableEq V] in
theorem Symm.swap {c : V → V → Colour} (hc : Symm c) : Symm (fun x y => swapRB (c x y)) := by
  intro x y; simp only [hc x y]

omit [DecidableEq V] in
theorem Is33k.swap {c : V → V → Colour} {k : ℕ} {S : Finset V} (hS : Is33k c k S) :
    Is33k (fun x y => swapRB (c x y)) k S := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy z hz h1 h2 h3 e1 e2 e3
    exact hS.2.1 x hx y hy z hz h1 h2 h3 ((swapRB_eq_red _).mp e1) ((swapRB_eq_red _).mp e2)
      ((swapRB_eq_red _).mp e3)
  · intro x hx y hy z hz h1 h2 h3 e1 e2 e3
    exact hS.1 x hx y hy z hz h1 h2 h3 ((swapRB_eq_blue _).mp e1) ((swapRB_eq_blue _).mp e2)
      ((swapRB_eq_blue _).mp e3)
  · intro T hT hTg
    exact hS.2.2 T hT (fun x hx y hy hxy => (swapRB_eq_green _).mp (hTg x hx y hy hxy))

theorem colourDeg_swap_red (c : V → V → Colour) (S : Finset V) (v : V) :
    colourDeg (fun x y => swapRB (c x y)) red S v = colourDeg c blue S v := by
  unfold colourDeg
  simp only [swapRB_eq_red]

end Colourings

/-! ## Part 3: Ramsey inputs, valid lower bounds, `lem:delete` and `lem:line` -/

section Paper

/-- **Ramsey input** `R(3,3,k) ≤ B`, as an explicit hypothesis: every vertex set on
which a colouring (of a complete graph) has no red triangle, no blue triangle and
no green `K_k` has fewer than `B` vertices. -/
def Bound33 (k B : ℕ) : Prop :=
  ∀ (W : Type) [DecidableEq W] (c : W → W → Colour), Symm c →
    ∀ S : Finset W, Is33k c k S → S.card < B

/-- **Ramsey input** `R(3,k) = R(2,3,k) ≤ B`, as an explicit hypothesis: every
vertex set on which a colouring has no red edge, no blue triangle and no green
`K_k` has fewer than `B` vertices.  (With `B = D + 1`, `D` is the common red and
blue cap `D_1 = D_2` for `t = (3,3,k)`.) -/
def BoundRB (k B : ℕ) : Prop :=
  ∀ (W : Type) [DecidableEq W] (c : W → W → Colour), Symm c →
    ∀ S : Finset W, NoColourEdge c red S → NoMonoTri c blue S → NoGreenK c k S → S.card < B

/-- `m` is a **valid lower bound** for order `n` (the paper's `m_k(n)`): `e(H) ≥ m` in
every `(3,3,k;n)`-colouring.  A `(3,3,k;n)`-colouring is a symmetric colouring
`c` of an `n`-element vertex set `S` (of any type `W`) with no red or blue
triangle and no green `K_k` on `S`. -/
def ValidLowerBound (k n : ℕ) (m : ℝ) : Prop :=
  ∀ (W : Type) [DecidableEq W] (c : W → W → Colour), Symm c →
    ∀ S : Finset W, S.card = n → Is33k c k S → m ≤ (eH c S : ℝ)

variable {W : Type} [DecidableEq W]

/-- The red and blue degrees are at most the cap `D` (Lemma `lem:caps`, `D_1 = D_2`). -/
theorem colourDeg_le_of_boundRB {k D : ℕ} (hD : BoundRB k (D + 1)) {c : W → W → Colour}
    (hc : Symm c) {S : Finset W} (hS : Is33k c k S) {v : W} (hv : v ∈ S) :
    colourDeg c red S v ≤ D ∧ colourDeg c blue S v ≤ D := by
  have hred : ∀ c' : W → W → Colour, Symm c' → Is33k c' k S → colourDeg c' red S v ≤ D := by
    intro c' hc' hS'
    obtain ⟨h1, h2, h3⟩ := redNbhd_props hS' hv
    have := hD W c' hc' _ h1 h2 h3
    unfold colourDeg; omega
  refine ⟨hred c hc hS, ?_⟩
  rw [← colourDeg_swap_red]
  exact hred _ hc.swap hS.swap

/-- The green degree is below `B` when `R(3,3,k-1) ≤ B` (Lemma `lem:caps`, `D_3`). -/
theorem greenDeg_lt_of_bound33 {k B : ℕ} (hB : Bound33 (k - 1) B) {c : W → W → Colour}
    (hc : Symm c) {S : Finset W} (hS : Is33k c k S) {v : W} (hv : v ∈ S) :
    colourDeg c green S v < B :=
  hB W c hc _ (greenNbhd_is33 hc hS hv)

/-- **Lemma `lem:delete`(a).**  Let `n ≥ 1` and let `m n'` be a valid lower bound
for each `n' < n`.  If `R(3,3,k-1) ≤ B` (hypothesis `Bound33 (k-1) B`), then
`m (n-1) + max 0 (n - B)` is a valid lower bound for order `n`. -/
theorem lem_delete_a (k n B : ℕ) (m : ℕ → ℝ) (hn : 1 ≤ n) (hB : Bound33 (k - 1) B)
    (hm : ∀ n' < n, ValidLowerBound k n' (m n')) :
    ValidLowerBound k n (m (n - 1) + max 0 ((n : ℝ) - B)) := by
  intro W _ c hc S hSn hS
  obtain ⟨v, hv⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have he := eH_erase hc hv
  have hm' := hm (n - 1) (by omega) W c hc (S.erase v)
    (by rw [Finset.card_erase_of_mem hv, hSn]) (hS.mono (Finset.erase_subset v S))
  have h1 := hdeg_add_greenDeg c hv
  have h2 := greenDeg_lt_of_bound33 hB hc hS hv
  have h3 : (n : ℝ) - B ≤ hdeg c S v := by
    have : n ≤ hdeg c S v + B := by omega
    have : (n : ℝ) ≤ hdeg c S v + B := by exact_mod_cast this
    linarith
  have h4 : max 0 ((n : ℝ) - B) ≤ hdeg c S v := max_le (Nat.cast_nonneg _) h3
  rw [he]; push_cast; linarith

/-- **Lemma `lem:delete`(b).**  Let `m n'` be a valid lower bound for each `n' < n`.
For `2 ≤ s < n`, `⌈m s · n(n-1) / (s(s-1))⌉` is a valid lower bound for order `n`. -/
theorem lem_delete_b (k n s : ℕ) (m : ℕ → ℝ) (hs : 2 ≤ s) (hsn : s < n)
    (hm : ∀ n' < n, ValidLowerBound k n' (m n')) :
    ValidLowerBound k n
      ((⌈m s * ((n : ℝ) * ((n : ℝ) - 1)) / ((s : ℝ) * ((s : ℝ) - 1))⌉ : ℤ) : ℝ) := by
  intro W _ c hc S hSn hS
  set C := (n - 2).choose (s - 2) with hCdef
  have hsum : ∑ T ∈ S.powersetCard s, eH c T = C * eH c S := by
    rw [hCdef, ← hSn]; exact sum_ecount_powersetCard (nongreen_symm hc) S hs
  have hlow : ∀ T ∈ S.powersetCard s, m s ≤ (eH c T : ℝ) := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    exact hm s hsn W c hc T hT.2 (hS.mono hT.1)
  have h1 : ((S.powersetCard s).card : ℝ) * m s ≤ (C : ℝ) * eH c S := by
    have := Finset.sum_le_sum hlow
    rw [Finset.sum_const, nsmul_eq_mul] at this
    calc _ ≤ ∑ T ∈ S.powersetCard s, (eH c T : ℝ) := this
      _ = ((∑ T ∈ S.powersetCard s, eH c T : ℕ) : ℝ) := by push_cast; rfl
      _ = _ := by rw [hsum]; push_cast; ring
  rw [Finset.card_powersetCard, hSn] at h1
  have h1n : 1 ≤ n := by omega
  have h1s : 1 ≤ s := by omega
  have hid' : (n.choose s : ℝ) * ((s : ℝ) * ((s : ℝ) - 1)) = (n : ℝ) * ((n : ℝ) - 1) * C := by
    have := congrArg (Nat.cast : ℕ → ℝ) (choose_mul_two n s hs hsn.le)
    push_cast [Nat.cast_sub h1n, Nat.cast_sub h1s] at this
    rw [hCdef]; exact this
  have hCpos : (0 : ℝ) < C := by
    rw [hCdef]; exact_mod_cast Nat.choose_pos (by omega : s - 2 ≤ n - 2)
  have hss : (0 : ℝ) < (s : ℝ) * ((s : ℝ) - 1) := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith
  have key : m s * ((n : ℝ) * ((n : ℝ) - 1)) ≤ (eH c S : ℝ) * ((s : ℝ) * ((s : ℝ) - 1)) := by
    have h2 : (C : ℝ) * (m s * ((n : ℝ) * ((n : ℝ) - 1))) ≤
        (C : ℝ) * ((eH c S : ℝ) * ((s : ℝ) * ((s : ℝ) - 1))) := by
      have := mul_le_mul_of_nonneg_right h1 hss.le
      calc (C : ℝ) * (m s * ((n : ℝ) * ((n : ℝ) - 1)))
          = (n.choose s : ℝ) * ((s : ℝ) * ((s : ℝ) - 1)) * m s := by rw [hid']; ring
        _ = (n.choose s : ℝ) * m s * ((s : ℝ) * ((s : ℝ) - 1)) := by ring
        _ ≤ (C : ℝ) * eH c S * ((s : ℝ) * ((s : ℝ) - 1)) := this
        _ = _ := by ring
    exact le_of_mul_le_mul_left h2 hCpos
  have hdiv : m s * ((n : ℝ) * ((n : ℝ) - 1)) / ((s : ℝ) * ((s : ℝ) - 1)) ≤ (eH c S : ℝ) := by
    rw [div_le_iff₀ hss]; exact key
  have : ⌈m s * ((n : ℝ) * ((n : ℝ) - 1)) / ((s : ℝ) * ((s : ℝ) - 1))⌉ ≤ (eH c S : ℤ) :=
    Int.ceil_le.mpr (by exact_mod_cast hdiv)
  exact_mod_cast this

/-! ### `lem:line` -/

/-- `h` is **admissible** (as an `H`-degree) for order `n`, with common red/blue cap
`D` and green cap `D3`: `max(0, n-1-D3) ≤ h ≤ min(n-1, 2D)`. -/
def Admissible (n D D3 h : ℕ) : Prop :=
  max 0 ((n : ℤ) - 1 - D3) ≤ (h : ℤ) ∧ (h : ℤ) ≤ min ((n : ℤ) - 1) (2 * D)

/-- Every `h_v` is admissible, given `R(3,k) ≤ D + 1` and `R(3,3,k-1) ≤ D3 + 1`
(the caps `d_1(v), d_2(v) ≤ D` and `z_v ≤ D3` of Lemma `lem:caps`). -/
theorem hdeg_admissible {k D D3 : ℕ} (hD : BoundRB k (D + 1)) (hD3 : Bound33 (k - 1) (D3 + 1))
    {c : W → W → Colour} (hc : Symm c) {S : Finset W} (hS : Is33k c k S) {v : W}
    (hv : v ∈ S) : Admissible S.card D D3 (hdeg c S v) := by
  have h1 := hdeg_add_greenDeg c hv
  have h2 := greenDeg_lt_of_bound33 hD3 hc hS hv
  have h3 := colourDeg_le_of_boundRB hD hc hS hv
  have h4 := hdeg_eq_red_add_blue c S v
  unfold Admissible
  omega

/-- `lem:line`(a), arithmetic core: for any degree sequence `h` on `S` with
`∑ h = 2e`, all values admissible (`adm`), `∑ f(h_v) ≤ 0`, `β > 0` and
`f ≥ α - β·` on admissible values, `|S| α / (2β) ≤ e`. -/
theorem lem_line_core_a {ι : Type*} (S : Finset ι) (h : ι → ℕ) (e : ℕ)
    (hhand : ∑ v ∈ S, h v = 2 * e) (adm : ℕ → Prop) (hadm : ∀ v ∈ S, adm (h v))
    (f : ℕ → ℝ) (hsum : ∑ v ∈ S, f (h v) ≤ 0) (α β : ℝ) (hβ : 0 < β)
    (hline : ∀ x, adm x → α - β * x ≤ f x) :
    (S.card : ℝ) * α / (2 * β) ≤ e := by
  have h1 : ∑ v ∈ S, (α - β * (h v : ℝ)) ≤ ∑ v ∈ S, f (h v) :=
    Finset.sum_le_sum fun v hv => hline _ (hadm v hv)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h1
  have h2 : (∑ v ∈ S, (h v : ℝ)) = 2 * e := by exact_mod_cast hhand
  rw [h2] at h1
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- `lem:line`(b), arithmetic core: a nonempty sum of positive terms is positive. -/
theorem lem_line_core_b {ι : Type*} (S : Finset ι) (hne : S.Nonempty) (h : ι → ℕ)
    (adm : ℕ → Prop) (hadm : ∀ v ∈ S, adm (h v)) (f : ℕ → ℝ) (hsum : ∑ v ∈ S, f (h v) ≤ 0)
    (hpos : ∀ x, adm x → 0 < f x) : False := by
  have := Finset.sum_pos (fun v hv => hpos _ (hadm v hv)) hne
  linarith

/-- **Lemma `lem:line`(a).**  Let `f` be such that every `(3,3,k;n)`-colouring has
`∑_v f(h_v) ≤ 0`.  Assume the Ramsey inputs `R(3,k) ≤ D + 1` and
`R(3,3,k-1) ≤ D3 + 1` that define admissibility.  If `β > 0` and
`f(h) ≥ α - β h` for every admissible `h`, then every `(3,3,k;n)`-colouring has
`e(H) ≥ nα/(2β)`, and `⌈nα/(2β)⌉` is a valid lower bound `m_k(n)`. -/
theorem lem_line_a (k n D D3 : ℕ) (hD : BoundRB k (D + 1)) (hD3 : Bound33 (k - 1) (D3 + 1))
    (f : ℕ → ℝ)
    (hf : ∀ (W : Type) [DecidableEq W] (c : W → W → Colour), Symm c →
      ∀ S : Finset W, S.card = n → Is33k c k S → ∑ v ∈ S, f (hdeg c S v) ≤ 0)
    (α β : ℝ) (hβ : 0 < β) (hline : ∀ h, Admissible n D D3 h → α - β * h ≤ f h) :
    (∀ (W : Type) [DecidableEq W] (c : W → W → Colour), Symm c →
      ∀ S : Finset W, S.card = n → Is33k c k S → (n : ℝ) * α / (2 * β) ≤ eH c S) ∧
    ValidLowerBound k n ((⌈(n : ℝ) * α / (2 * β)⌉ : ℤ) : ℝ) := by
  have key : ∀ (W : Type) [DecidableEq W] (c : W → W → Colour), Symm c →
      ∀ S : Finset W, S.card = n → Is33k c k S → (n : ℝ) * α / (2 * β) ≤ eH c S := by
    intro W _ c hc S hSn hS
    have := lem_line_core_a S (hdeg c S) (eH c S) (sum_hdeg hc S) (Admissible n D D3)
      (fun v hv => hSn ▸ hdeg_admissible hD hD3 hc hS hv) f (hf W c hc S hSn hS) α β hβ hline
    rwa [hSn] at this
  refine ⟨key, ?_⟩
  intro W _ c hc S hSn hS
  have h1 := key W c hc S hSn hS
  have : ⌈(n : ℝ) * α / (2 * β)⌉ ≤ (eH c S : ℤ) := Int.ceil_le.mpr (by exact_mod_cast h1)
  exact_mod_cast this

/-- **Lemma `lem:line`(b).**  With `f`, `D`, `D3` as in `lem_line_a`: if `n ≥ 1` and
`f(h) > 0` for every admissible `h`, then no `(3,3,k;n)`-colouring exists. -/
theorem lem_line_b (k n D D3 : ℕ) (hD : BoundRB k (D + 1)) (hD3 : Bound33 (k - 1) (D3 + 1))
    (f : ℕ → ℝ)
    (hf : ∀ (W : Type) [DecidableEq W] (c : W → W → Colour), Symm c →
      ∀ S : Finset W, S.card = n → Is33k c k S → ∑ v ∈ S, f (hdeg c S v) ≤ 0)
    (hn : 1 ≤ n) (hpos : ∀ h, Admissible n D D3 h → 0 < f h) :
    ∀ (W : Type) [DecidableEq W] (c : W → W → Colour), Symm c →
      ∀ S : Finset W, S.card = n → ¬ Is33k c k S := by
  intro W _ c hc S hSn hS
  exact lem_line_core_b S (Finset.card_pos.mp (by omega)) (hdeg c S) (Admissible n D D3)
    (fun v hv => hSn ▸ hdeg_admissible hD hD3 hc hS hv) f (hf W c hc S hSn hS) hpos

end Paper

/-! ## Part 4: bridges from the conventional definition of Ramsey numbers -/

section Bridge

/-- A clique of colour `a`. -/
def ColourClique {X : Type*} (c : X → X → Colour) (a : Colour) (U : Finset X) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, x ≠ y → c x y = a

/-- The conventional statement `R(t₁,t₂,t₃) ≤ B`: every colouring of the edges of
`K_B` (vertex set `Fin B`) has, for some colour `i`, a `K_{t_i}` of colour `i`. -/
def RamseyLE (t₁ t₂ t₃ B : ℕ) : Prop :=
  ∀ c : Fin B → Fin B → Colour, Symm c →
    ∃ U : Finset (Fin B), (U.card = t₁ ∧ ColourClique c red U) ∨
      (U.card = t₂ ∧ ColourClique c blue U) ∨ (U.card = t₃ ∧ ColourClique c green U)

theorem exists_fin_embedding {X : Type} (S : Finset X) {B : ℕ} (h : B ≤ S.card) :
    ∃ g : Fin B ↪ X, ∀ i, g i ∈ S := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin B) (β := S) (by simpa using h)
  exact ⟨e.trans (Function.Embedding.subtype _), fun i => (e i).2⟩

theorem colourClique_map {X : Type} {c : X → X → Colour} {B : ℕ} (g : Fin B ↪ X) {a : Colour}
    {U : Finset (Fin B)} (hU : ColourClique (fun i j => c (g i) (g j)) a U) :
    ColourClique c a (U.map g) := by
  intro x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
  exact hU i hi j hj (fun h => hxy (h ▸ rfl))

theorem false_of_noMonoTri {X : Type} [DecidableEq X] {c : X → X → Colour} {a : Colour}
    {S U : Finset X} (h : NoMonoTri c a S) (hUS : U ⊆ S) (hU3 : U.card = 3)
    (hU : ColourClique c a U) : False := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hU3
  exact h x (hUS (by simp)) y (hUS (by simp)) z (hUS (by simp)) hxy hxz hyz
    (hU x (by simp) y (by simp) hxy) (hU x (by simp) z (by simp) hxz)
    (hU y (by simp) z (by simp) hyz)

theorem false_of_noColourEdge {X : Type} [DecidableEq X] {c : X → X → Colour} {a : Colour}
    {S U : Finset X} (h : NoColourEdge c a S) (hUS : U ⊆ S) (hU2 : U.card = 2)
    (hU : ColourClique c a U) : False := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hU2
  exact h x (hUS (by simp)) y (hUS (by simp)) hxy (hU x (by simp) y (by simp) hxy)

theorem map_subset_of_mem {X : Type} {S : Finset X} {B : ℕ} (g : Fin B ↪ X) (hg : ∀ i, g i ∈ S)
    (U : Finset (Fin B)) : U.map g ⊆ S := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
  exact hg i

/-- Bridge: the conventional `R(3,3,k) ≤ B` gives the hypothesis `Bound33 k B`. -/
theorem bound33_of_ramseyLE {k B : ℕ} (hR : RamseyLE 3 3 k B) : Bound33 k B := by
  intro X _ c hc S hS
  by_contra hlt
  obtain ⟨g, hg⟩ := exists_fin_embedding S (not_lt.mp hlt)
  obtain ⟨U, hU⟩ := hR (fun i j => c (g i) (g j)) (fun i j => hc _ _)
  rcases hU with ⟨h3, hU⟩ | ⟨h3, hU⟩ | ⟨hk, hU⟩
  · exact false_of_noMonoTri hS.1 (map_subset_of_mem g hg U) (by rw [Finset.card_map, h3])
      (colourClique_map g hU)
  · exact false_of_noMonoTri hS.2.1 (map_subset_of_mem g hg U) (by rw [Finset.card_map, h3])
      (colourClique_map g hU)
  · have := hS.2.2 _ (map_subset_of_mem g hg U) (colourClique_map g hU)
    rw [Finset.card_map, hk] at this
    exact lt_irrefl _ this

/-- Bridge: the conventional `R(2,3,k) ≤ B` (and `R(2,3,k) = R(3,k)`) gives the
hypothesis `BoundRB k B`. -/
theorem boundRB_of_ramseyLE {k B : ℕ} (hR : RamseyLE 2 3 k B) : BoundRB k B := by
  intro X _ c hc S hred hblue hgreen
  by_contra hlt
  obtain ⟨g, hg⟩ := exists_fin_embedding S (not_lt.mp hlt)
  obtain ⟨U, hU⟩ := hR (fun i j => c (g i) (g j)) (fun i j => hc _ _)
  rcases hU with ⟨h2, hU⟩ | ⟨h3, hU⟩ | ⟨hk, hU⟩
  · exact false_of_noColourEdge hred (map_subset_of_mem g hg U) (by rw [Finset.card_map, h2])
      (colourClique_map g hU)
  · exact false_of_noMonoTri hblue (map_subset_of_mem g hg U) (by rw [Finset.card_map, h3])
      (colourClique_map g hU)
  · have := hgreen _ (map_subset_of_mem g hg U) (colourClique_map g hU)
    rw [Finset.card_map, hk] at this
    exact lt_irrefl _ this

end Bridge

#print axioms lem_cert_core
#print axioms lem_cert
#print axioms greenClique_decomp
#print axioms greenClique_card_le_of_certifiers
#print axioms ecount_erase
#print axioms sum_ecount_powersetCard
#print axioms lem_delete_a
#print axioms lem_delete_b
#print axioms hdeg_admissible
#print axioms lem_line_core_a
#print axioms lem_line_core_b
#print axioms lem_line_a
#print axioms lem_line_b
#print axioms bound33_of_ramseyLE
#print axioms boundRB_of_ramseyLE

end RamseyLean.Lemmas
