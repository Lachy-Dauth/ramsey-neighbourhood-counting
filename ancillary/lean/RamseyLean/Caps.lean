import Mathlib.Tactic
import RamseyLean.LocalCombinatorics

/-!
# Local caps, the handshake corollary, caps on several neighbourhoods, and corner identities

This file formalises, from Section `sec:prelim` of
`paper/neighbourhood_counting.tex`:

* Lemma `lem:caps` (local caps `D_i` and `C_ij`): `local_caps`, `local_caps_degree`,
  `local_caps_common`;
* Corollary `cor:handshake`: `handshake_cap`;
* Lemma `lem:multicaps` (caps on several neighbourhoods): `multicaps`;
* Lemma `lem:corners` (corner identities): `corner_choose`, `corner_mono`, `corner_mixed`,
  `corner_apex`, bundled for three colours as `corner_identities`.

Also: the examples after Lemma `lem:caps` for `t = (3,3,k)` with all hypotheses discharged
(`cap_C12_33k`, `cap_C21_33k`: `C_12 = C_21 = k - 1`; `cap_C11_33k`, `cap_C22_33k`:
`C_11 = C_22 = 0`), and a bridge `avoids_33k_iff` to the definitions of
`LocalCombinatorics.lean` (`NoMonoTriangle`, `AvoidsGreenK`).

The versions with the paper's constants `R(·) - 1` (for the conventional `ramseyNumber`, given
that it exists) are `local_caps_degree_R`, `local_caps_common_R`, `handshake_cap_R` and
`multicaps_R`. The remark after Lemma `lem:multicaps` (Lemma `lem:caps` is its case `|Y| ≤ 2`)
is `multicaps_singleton`, `multicaps_pair`, `local_caps_degree_via_multicaps` and
`local_caps_common_via_multicaps`.

`M_i`, `T_{i,j}` and `X` are cardinalities of sets of 3-element vertex sets, and `e_j(S)` is a
cardinality of a set of 2-element subsets of `S`. The double counts of the paper (corners at
vertices versus corners in triangles; the handshake lemma) are the bijection `sum_pointed`
between pairs `(v, R)` with `v ∉ R` and pairs `(S, v)` with `v ∈ S`.

All declarations live in the namespace `RamseyLean.Caps`, so that the short names
(`nbhd`, `deg`, `e`, `M`, `T`, `X`, `AvoidsOn`, ...) do not clash with sibling files.

## Conventions

A colouring of `E(K_V)` is a function `c : V → V → κ` with `c x y = c y x`.
Its diagonal values are never used: every definition below only reads `c x y` for `x ≠ y`.
`κ` is an arbitrary type of colours for the cap lemmas (the paper's case is three colours);
the mixed corner identity, which is specific to three colours, uses `RamseyLocal.Colour`.

A vector `t = (t_1, t_2, t_3)` is a function `t : κ → ℕ`, and the paper's
`t - e_i - e_j` is literally `t - Pi.single i 1 - Pi.single j 1` (pointwise truncated
subtraction). The paper's hypothesis `t_l ≥ 3` in Lemma `lem:caps` only ensures that no entry
is truncated; the Lean statements do not need it (in degenerate cases their hypotheses are
contradictory or the cap is vacuous).

## How Ramsey numbers enter

Only as explicit cap hypotheses of the form
`∀ S : Finset V, AvoidsOn c s S → S.card ≤ B`, i.e. "every vertex set on which `c` is
`s`-avoiding has at most `B` vertices", which is exactly what the paper uses
(`|S| ≤ R(s) - 1`, or `≤ B - 1` from a proven bound `R(s) ≤ B`).
The bridge lemmas `cap_of_ramseyLE` and `cap_of_ramseyNumber` derive such a hypothesis
from the conventional definition of `R(s) ≤ n` / of `R(s)` as a least number.
-/

namespace RamseyLean.Caps

open Finset

section Defs

variable {V κ : Type*}

/-- `K` is a colour-`l` clique: every edge inside `K` has colour `l`. -/
def IsClique (c : V → V → κ) (l : κ) (K : Finset V) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, x ≠ y → c x y = l

instance [DecidableEq V] [DecidableEq κ] (c : V → V → κ) (l : κ) :
    DecidablePred (IsClique c l) := fun K => by
  unfold IsClique; infer_instance

/-- `c` is `s`-avoiding on the vertex set `S`: for no colour `l` does `S` contain a
colour-`l` clique on `s l` (or more) vertices. -/
def AvoidsOn (c : V → V → κ) (s : κ → ℕ) (S : Finset V) : Prop :=
  ∀ l, ∀ K ⊆ S, IsClique c l K → K.card < s l

/-- `c` is `t`-avoiding (a `(t; n)`-colouring). -/
def Avoids [Fintype V] (c : V → V → κ) (t : κ → ℕ) : Prop :=
  AvoidsOn c t univ

variable [Fintype V] [DecidableEq V] [DecidableEq κ]

/-- The colour-`i` neighbourhood `N_i(v)` (it never contains `v`). -/
def nbhd (c : V → V → κ) (i : κ) (v : V) : Finset V :=
  univ.filter fun w => w ≠ v ∧ c v w = i

/-- The colour-`i` degree `d_i(v)`. -/
def deg (c : V → V → κ) (i : κ) (v : V) : ℕ := (nbhd c i v).card

/-- The colour-`j` edges inside `S`, as 2-element subsets of `S`. -/
def edgesIn (c : V → V → κ) (j : κ) (S : Finset V) : Finset (Finset V) :=
  (S.powersetCard 2).filter (IsClique c j)

/-- `e_j(S)`, the number of colour-`j` edges inside `S`. -/
def e (c : V → V → κ) (j : κ) (S : Finset V) : ℕ := (edgesIn c j S).card

/-- The triangles of `K_V`, i.e. its 3-element vertex sets. -/
def triangles : Finset (Finset V) := (univ : Finset V).powersetCard 3

/-- `M_i`: the number of triangles all of whose edges have colour `i`. -/
def M (c : V → V → κ) (i : κ) : ℕ := (triangles.filter (IsClique c i)).card

/-- `v` is an `(i,j)`-apex of the triangle `S`: both edges of `S` at `v` have colour `i`,
and the third edge (the edge of `S.erase v`) has colour `j`. -/
def IsApex (c : V → V → κ) (i j : κ) (S : Finset V) (v : V) : Prop :=
  (∀ u ∈ S.erase v, c v u = i) ∧ IsClique c j (S.erase v)

instance (c : V → V → κ) (i j : κ) (S : Finset V) : DecidablePred (IsApex c i j S) :=
  fun v => by unfold IsApex; infer_instance

/-- `T_{i,j}` (for `i ≠ j`): the number of triangles with two edges of colour `i`, meeting at
the apex, and one edge of colour `j`. -/
def T (c : V → V → κ) (i j : κ) : ℕ :=
  (triangles.filter fun S => ∃ v ∈ S, IsApex c i j S v).card

/-- A triangle is rainbow when its three edges have three different colours; equivalently, any
two of its edges (which always meet at a vertex `y`) have different colours. -/
def IsRainbow (c : V → V → κ) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z → c x y ≠ c y z

instance (c : V → V → κ) : DecidablePred (IsRainbow c) := fun S => by
  unfold IsRainbow; infer_instance

/-- `X`: the number of rainbow triangles. -/
def X (c : V → V → κ) : ℕ := (triangles.filter (IsRainbow c)).card

end Defs

/-! ## Pointed sets: the double count behind the handshake lemma and the corner identities -/

section Pointed

variable {V : Type*} [DecidableEq V]

/-- Counting pairs `(v, R)` with `R` a `k`-subset of `U \ {v}` is the same as counting pairs
`(S, v)` with `S` a `(k+1)`-subset of `U` and `v ∈ S` (via `S = insert v R`, `R = S.erase v`). -/
theorem sum_pointed (U : Finset V) (k : ℕ) (Q : V → Finset V → Prop)
    [∀ v, DecidablePred (Q v)] :
    ∑ v ∈ U, (((U.erase v).powersetCard k).filter (Q v)).card =
      ∑ S ∈ U.powersetCard (k + 1), (S.filter fun v => Q v (S.erase v)).card := by
  rw [← card_sigma, ← card_sigma]
  refine card_nbij' (fun p => ⟨insert p.1 p.2, p.1⟩) (fun q => ⟨q.2, q.1.erase q.2⟩)
    ?_ ?_ ?_ ?_
  · rintro ⟨v, R⟩ h
    simp only [mem_coe, mem_sigma, mem_filter, mem_powersetCard] at h ⊢
    obtain ⟨hv, ⟨hRU, hcard⟩, hQ⟩ := h
    have hvR : v ∉ R := fun hm => (notMem_erase v U) (hRU hm)
    refine ⟨⟨insert_subset hv (hRU.trans (erase_subset v U)), ?_⟩, mem_insert_self v R, ?_⟩
    · rw [card_insert_of_notMem hvR, hcard]
    · rwa [erase_insert hvR]
  · rintro ⟨S, v⟩ h
    simp only [mem_coe, mem_sigma, mem_filter, mem_powersetCard] at h ⊢
    obtain ⟨⟨hSU, hcard⟩, hv, hQ⟩ := h
    refine ⟨hSU hv, ⟨erase_subset_erase v hSU, ?_⟩, hQ⟩
    rw [card_erase_of_mem hv, hcard]; rfl
  · rintro ⟨v, R⟩ h
    simp only [mem_coe, mem_sigma, mem_filter, mem_powersetCard] at h
    have hvR : v ∉ R := fun hm => (notMem_erase v U) (h.2.1.1 hm)
    simp [erase_insert hvR]
  · rintro ⟨S, v⟩ h
    simp only [mem_coe, mem_sigma, mem_filter, mem_powersetCard] at h
    simp [insert_erase h.2.1]

end Pointed

/-! ## Lemma `lem:caps`, Corollary `cor:handshake`, Lemma `lem:multicaps` -/

section Caps

variable {V κ : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]

theorem mem_nbhd {c : V → V → κ} {i : κ} {v w : V} :
    w ∈ nbhd c i v ↔ w ≠ v ∧ c v w = i := by
  simp [nbhd]

omit [Fintype V] [DecidableEq V] [DecidableEq κ] in
theorem AvoidsOn.mono_set {c : V → V → κ} {s : κ → ℕ} {S S' : Finset V}
    (h : AvoidsOn c s S) (hS : S' ⊆ S) : AvoidsOn c s S' :=
  fun l K hK hcl => h l K (hK.trans hS) hcl

omit [DecidableEq κ] in
/-- The common core of the proofs of Lemmas `lem:caps` and `lem:multicaps`.
If every vertex of `S` is joined in colour `l` to every vertex of a colour-`l` clique `W l`
disjoint from `S`, then a colour-`l` clique in `S` together with `W l` is a colour-`l`
clique; so on `S` the colouring avoids `s` whenever `t l ≤ s l + |W l|`. -/
theorem avoidsOn_of_join (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (t s : κ → ℕ)
    (hav : Avoids c t) (S : Finset V) (W : κ → Finset V)
    (hW : ∀ l, IsClique c l (W l)) (hdisj : ∀ l, Disjoint S (W l))
    (hjoin : ∀ l, ∀ x ∈ S, ∀ y ∈ W l, c x y = l) (hs : ∀ l, t l ≤ s l + (W l).card) :
    AvoidsOn c s S := by
  intro l K hKS hK
  have hcl : IsClique c l (K ∪ W l) := by
    intro x hx y hy hxy
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · exact hK x hx y hy hxy
    · exact hjoin l x (hKS hx) y hy
    · rw [hc]; exact hjoin l y (hKS hy) x hx
    · exact hW l x hx y hy hxy
  have h1 := hav l (K ∪ W l) (subset_univ _) hcl
  have hd : Disjoint K (W l) := (hdisj l).mono_left hKS
  rw [card_union_of_disjoint hd] at h1
  have := hs l
  omega

/-- Lemma `lem:caps`, first part: `d_i(v) ≤ D_i`, where `D_i` is any number such that every
vertex set on which `c` is `(t - e_i)`-avoiding has at most `D_i` vertices
(the paper takes `D_i = R(t - e_i) - 1`). -/
theorem local_caps_degree (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (t : κ → ℕ)
    (hav : Avoids c t) (i : κ) (D : ℕ)
    (hD : ∀ S : Finset V, AvoidsOn c (t - Pi.single i 1) S → S.card ≤ D) (v : V) :
    deg c i v ≤ D := by
  apply hD
  refine avoidsOn_of_join c hc t _ hav (nbhd c i v) (fun l => if l = i then {v} else ∅)
    ?_ ?_ ?_ ?_
  · intro l; dsimp only; split_ifs <;> intro x hx y hy hxy <;> simp_all
  · intro l; dsimp only; split_ifs
    · simp [mem_nbhd]
    · simp
  · intro l x hx y hy
    dsimp only at hy
    split_ifs at hy with hl
    · rw [mem_singleton] at hy; subst hy hl; rw [hc]; exact (mem_nbhd.mp hx).2
    · simp at hy
  · intro l
    by_cases hl : l = i
    · subst hl; simp; omega
    · simp [hl]

/-- Lemma `lem:caps`, second part: for every colour `j` and every `u ∈ N_i(v)`,
`|N_i(v) ∩ N_j(u)| ≤ C_ij`, where `C_ij` is any number such that every vertex set on which `c`
is `(t - e_i - e_j)`-avoiding has at most `C_ij` vertices
(the paper takes `C_ij = R(t - e_i - e_j) - 1`). -/
theorem local_caps_common (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (t : κ → ℕ)
    (hav : Avoids c t) (i j : κ) (C : ℕ)
    (hC : ∀ S : Finset V, AvoidsOn c (t - Pi.single i 1 - Pi.single j 1) S → S.card ≤ C)
    (v u : V) (hu : u ∈ nbhd c i v) :
    (nbhd c i v ∩ nbhd c j u).card ≤ C := by
  obtain ⟨huv, hvu⟩ := mem_nbhd.mp hu
  apply hC
  refine avoidsOn_of_join c hc t _ hav (nbhd c i v ∩ nbhd c j u)
    (fun l => (if l = i then {v} else ∅) ∪ (if l = j then {u} else ∅)) ?_ ?_ ?_ ?_
  · intro l x hx y hy hxy
    dsimp only at hx hy
    have key : ∀ a ∈ ((if l = i then {v} else ∅) ∪ (if l = j then {u} else ∅) : Finset V),
        (a = v ∧ l = i) ∨ (a = u ∧ l = j) := by
      intro a ha; rw [mem_union] at ha; split_ifs at ha <;> simp_all
    rcases key x hx with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ <;>
      rcases key y hy with ⟨rfl, hl'⟩ | ⟨rfl, hl'⟩
    · exact absurd rfl hxy
    · rw [hvu]; exact hl.symm
    · rw [hc, hvu]; exact hl'.symm
    · exact absurd rfl hxy
  · intro l
    dsimp only
    rw [disjoint_union_right]
    constructor <;> split_ifs <;> simp [mem_nbhd]
  · intro l x hx y hy
    rw [mem_inter, mem_nbhd, mem_nbhd] at hx
    dsimp only at hy
    rcases mem_union.mp hy with hy | hy <;> split_ifs at hy with hl <;>
      simp only [mem_singleton, notMem_empty] at hy
    · subst hy hl; rw [hc]; exact hx.1.2
    · subst hy hl; rw [hc]; exact hx.2.2
  · intro l
    dsimp only
    by_cases hli : l = i <;> by_cases hlj : l = j
    · subst hli hlj
      have : ({v} ∪ {u} : Finset V).card = 2 := by
        rw [card_union_of_disjoint (disjoint_singleton.mpr (Ne.symm huv))]; rfl
      simp only [if_true, this, Pi.sub_apply, Pi.single_eq_same]
      omega
    · subst hli
      simp [hlj]
      omega
    · subst hlj
      simp [hli]
      omega
    · simp [hli, hlj]

omit [Fintype V] [DecidableEq κ] in
theorem isClique_pair (c : V → V → κ) (hc : ∀ x y, c x y = c y x) {l : κ} {x y : V}
    (hxy : x ≠ y) : IsClique c l {x, y} ↔ c x y = l := by
  constructor
  · intro h; exact h x (by simp) y (by simp) hxy
  · intro h p hp q hq hpq
    simp only [mem_insert, mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd rfl hpq
    · exact h
    · rw [hc]; exact h
    · exact absurd rfl hpq

/-- The handshake lemma inside a vertex set `S`: summing over `u ∈ S` the number of colour-`j`
neighbours of `u` in `S` counts every colour-`j` edge of `S` twice. -/
theorem handshake (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (j : κ) (S : Finset V) :
    ∑ u ∈ S, (S ∩ nbhd c j u).card = 2 * e c j S := by
  have h1 : ∀ u ∈ S, (S ∩ nbhd c j u).card =
      (((S.erase u).powersetCard 1).filter fun R => ∀ w ∈ R, c u w = j).card := by
    intro u _
    rw [powersetCard_one, filter_map, card_map]
    congr 1
    ext w
    simp only [mem_inter, mem_nbhd, mem_filter, mem_erase, Function.comp_apply,
      Function.Embedding.coeFn_mk, mem_singleton, forall_eq]
    tauto
  rw [sum_congr rfl h1, sum_pointed S 1 (fun u R => ∀ w ∈ R, c u w = j)]
  have h2 : ∀ T ∈ S.powersetCard (1 + 1),
      (T.filter fun v => ∀ w ∈ T.erase v, c v w = j).card =
        if IsClique c j T then 2 else 0 := by
    intro T hT
    rw [mem_powersetCard] at hT
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hT.2
    have hx : ({x, y} : Finset V).erase x = {y} := by
      rw [erase_insert (by simpa using hxy)]
    have hy : ({x, y} : Finset V).erase y = {x} := by
      rw [erase_insert_of_ne hxy, erase_singleton, insert_empty]
    rw [card_filter, sum_insert (by simpa using hxy), sum_singleton, hx, hy]
    simp only [mem_singleton, forall_eq, isClique_pair c hc hxy]
    rw [hc y x]
    split_ifs <;> rfl
  rw [sum_congr rfl h2, ← sum_filter, sum_const, smul_eq_mul, mul_comm]
  rfl

/-- Corollary `cor:handshake`: `e_j(N_i(v)) ≤ ⌊C_ij d_i(v) / 2⌋` (natural-number division is
the floor), with `C_ij` given by an explicit cap hypothesis as in `local_caps_common`. -/
theorem handshake_cap (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (t : κ → ℕ)
    (hav : Avoids c t) (i j : κ) (C : ℕ)
    (hC : ∀ S : Finset V, AvoidsOn c (t - Pi.single i 1 - Pi.single j 1) S → S.card ≤ C)
    (v : V) :
    e c j (nbhd c i v) ≤ C * deg c i v / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have h1 : ∑ u ∈ nbhd c i v, (nbhd c i v ∩ nbhd c j u).card ≤ ∑ _u ∈ nbhd c i v, C :=
    sum_le_sum fun u hu => local_caps_common c hc t hav i j C hC v u hu
  rw [handshake c hc j, sum_const, smul_eq_mul] at h1
  calc e c j (nbhd c i v) * 2 = 2 * e c j (nbhd c i v) := mul_comm _ _
    _ ≤ (nbhd c i v).card * C := h1
    _ = C * deg c i v := mul_comm _ _

/-- Lemma `lem:caps` (both parts together). -/
theorem local_caps (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (t : κ → ℕ)
    (hav : Avoids c t) (i : κ) (D : ℕ)
    (hD : ∀ S : Finset V, AvoidsOn c (t - Pi.single i 1) S → S.card ≤ D)
    (C : κ → ℕ)
    (hC : ∀ j, ∀ S : Finset V, AvoidsOn c (t - Pi.single i 1 - Pi.single j 1) S →
      S.card ≤ C j) (v : V) :
    deg c i v ≤ D ∧ ∀ j, ∀ u ∈ nbhd c i v, (nbhd c i v ∩ nbhd c j u).card ≤ C j :=
  ⟨local_caps_degree c hc t hav i D hD v,
    fun j u hu => local_caps_common c hc t hav i j (C j) (hC j) v u hu⟩

/-- `Y_l = {y ∈ Y : a(y) = l}`. -/
def colourClass (Y : Finset V) (a : V → κ) (l : κ) : Finset V := Y.filter fun y => a y = l

/-- The largest order of a colour-`l` clique contained in `A` (`0` if `A` is empty). -/
def maxCliqueOrder (c : V → V → κ) (l : κ) (A : Finset V) : ℕ :=
  (A.powerset.filter (IsClique c l)).sup card

/-- `⋂_{y ∈ Y} N_{a(y)}(y)`, the common neighbourhood of `Y` in the prescribed colours. -/
def commonNbhd (c : V → V → κ) (Y : Finset V) (a : V → κ) : Finset V :=
  univ.filter fun x => ∀ y ∈ Y, x ∈ nbhd c (a y) y

/-- The argument of Lemma `lem:multicaps` for arbitrary colour-`l` cliques `W l ⊆ Y_l`:
the common neighbourhood is `(t - |W|)`-avoiding, hence capped. -/
theorem multicaps_of_cliques (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (t : κ → ℕ)
    (hav : Avoids c t) (Y : Finset V) (a : V → κ) (W : κ → Finset V)
    (hWY : ∀ l, W l ⊆ colourClass Y a l) (hW : ∀ l, IsClique c l (W l)) (B : ℕ)
    (hB : ∀ S : Finset V, AvoidsOn c (t - fun l => (W l).card) S → S.card ≤ B) :
    (commonNbhd c Y a).card ≤ B := by
  have hmem : ∀ {l y}, y ∈ W l → y ∈ Y ∧ a y = l := fun hy => by
    simpa [colourClass] using hWY _ hy
  apply hB
  refine avoidsOn_of_join c hc t _ hav _ W hW ?_ ?_ ?_
  · intro l
    rw [disjoint_left]
    intro x hx hxW
    have := (mem_filter.mp hx).2 x (hmem hxW).1
    exact (mem_nbhd.mp this).1 rfl
  · intro l x hx y hy
    obtain ⟨hyY, hay⟩ := hmem hy
    have := (mem_nbhd.mp ((mem_filter.mp hx).2 y hyY)).2
    rw [hc, this, hay]
  · intro l
    simp only [Pi.sub_apply]
    omega

/-- Lemma `lem:multicaps` (caps on several neighbourhoods). Let `w_l` be the largest order of a
colour-`l` clique contained in `Y_l`. Then `S = ⋂_{y∈Y} N_{a(y)}(y)` has `|S| ≤ B`, where `B` is
any number such that every vertex set on which `c` is `(t - w)`-avoiding has at most `B`
vertices (the paper takes `B = R(t - w) - 1`).

The paper assumes `Y` nonempty; the statement below does not need this (for `Y = ∅` it is the
cap for `t` itself), and `a` is given on all of `V` but only its values on `Y` are used. -/
theorem multicaps (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (t : κ → ℕ)
    (hav : Avoids c t) (Y : Finset V) (a : V → κ) (B : ℕ)
    (hB : ∀ S : Finset V,
      AvoidsOn c (t - fun l => maxCliqueOrder c l (colourClass Y a l)) S → S.card ≤ B) :
    (commonNbhd c Y a).card ≤ B := by
  have hex : ∀ l, ∃ K ∈ (colourClass Y a l).powerset.filter (IsClique c l),
      maxCliqueOrder c l (colourClass Y a l) = K.card := fun l =>
    exists_mem_eq_sup _ ⟨∅, by simp [IsClique]⟩ card
  choose W hWmem hWcard using hex
  refine multicaps_of_cliques c hc t hav Y a W (fun l => ?_) (fun l => ?_) B ?_
  · exact mem_powerset.mp (mem_filter.mp (hWmem l)).1
  · exact (mem_filter.mp (hWmem l)).2
  · have : (fun l => (W l).card) = fun l => maxCliqueOrder c l (colourClass Y a l) :=
      funext fun l => (hWcard l).symm
    rw [this]; exact hB

end Caps

/-! ## Bridges from the conventional definition of Ramsey numbers, and two degenerate caps -/

section Bridge

variable {V κ : Type*}

/-- Conventional `R(s) ≤ n`: every colouring of `E(K_n)` (on the vertex set `Fin n`)
contains, for some colour `l`, a colour-`l` clique on `s l` vertices. -/
def RamseyLE (κ : Type*) (s : κ → ℕ) (n : ℕ) : Prop :=
  ∀ c : Fin n → Fin n → κ, (∀ x y, c x y = c y x) →
    ∃ l, ∃ K : Finset (Fin n), K.card = s l ∧ IsClique c l K

/-- The conventional Ramsey number `R(s)`: the least `n` with `R(s) ≤ n`. -/
noncomputable def ramseyNumber (κ : Type*) (s : κ → ℕ) : ℕ := sInf {n | RamseyLE κ s n}

/-- Bridge: a proven bound `R(s) ≤ B + 1` gives the cap hypothesis used above,
`|S| ≤ B` for every vertex set `S` on which `c` is `s`-avoiding. -/
theorem cap_of_ramseyLE {s : κ → ℕ} {B : ℕ} (h : RamseyLE κ s (B + 1))
    (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (S : Finset V) (hS : AvoidsOn c s S) :
    S.card ≤ B := by
  by_contra hlt
  obtain ⟨T, hTS, hTcard⟩ := exists_subset_card_eq (show B + 1 ≤ S.card by omega)
  let f : Fin (B + 1) ≃ T := (T.equivFin.trans (finCongr hTcard)).symm
  obtain ⟨l, K, hK, hcl⟩ := h (fun x y => c (f x) (f y)) (fun x y => hc _ _)
  let emb : Fin (B + 1) ↪ V := f.toEmbedding.trans (Function.Embedding.subtype _)
  have h1 := hS l (K.map emb) ?_ ?_
  · rw [card_map, hK] at h1; exact lt_irrefl _ h1
  · intro x hx
    obtain ⟨y, _, rfl⟩ := mem_map.mp hx
    exact hTS (f y).2
  · intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
    exact hcl x' hx' y' hy' (fun h => hxy (h ▸ rfl))

/-- Bridge: if `R(s)` exists (some `n` has `R(s) ≤ n`), every vertex set on which `c` is
`s`-avoiding has at most `R(s) - 1` vertices. -/
theorem cap_of_ramseyNumber {s : κ → ℕ} (hex : ∃ n, RamseyLE κ s n)
    (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (S : Finset V) (hS : AvoidsOn c s S) :
    S.card ≤ ramseyNumber κ s - 1 := by
  have hR : RamseyLE κ s (ramseyNumber κ s) := Nat.sInf_mem hex
  rcases hk : ramseyNumber κ s with _ | m
  · rw [hk] at hR
    obtain ⟨l, K, hK, -⟩ := hR (fun x => x.elim0) (fun x => x.elim0)
    have hK0 : K = ∅ := eq_empty_of_forall_notMem fun x => x.elim0
    have := hS l ∅ (empty_subset _) (by simp [IsClique])
    rw [← hK, hK0] at this
    exact absurd this (lt_irrefl _)
  · rw [hk] at hR
    exact cap_of_ramseyLE hR c hc S hS

/-- Forbidding cliques of order `≥ s l` is the same as forbidding cliques of order exactly
`s l` (the usual convention for "contains a `K_{s_l}`"). -/
theorem avoidsOn_iff_no_exact [DecidableEq V] (c : V → V → κ) (s : κ → ℕ) (S : Finset V) :
    AvoidsOn c s S ↔ ∀ l, ∀ K ⊆ S, K.card = s l → ¬ IsClique c l K := by
  constructor
  · intro h l K hK hcard hcl
    have := h l K hK hcl
    omega
  · intro h l K hK hcl
    by_contra hn
    obtain ⟨K', hK'K, hcard⟩ := exists_subset_card_eq (Nat.le_of_not_gt hn)
    exact h l K' (hK'K.trans hK) hcard fun x hx y hy hxy => hcl x (hK'K hx) y (hK'K hy) hxy

end Bridge

/-! ## The three-colour case `t = (3, 3, k)`: the degenerate caps `C_12 = k - 1`, `C_11 = 0` -/

section ThreeColour

open RamseyLocal (Colour)
open RamseyLocal.Colour

instance Colour.fintypeCaps : Fintype Colour :=
  ⟨{red, blue, green}, fun x => by cases x <;> decide⟩

/-- The vector `(a, b, d)` indexed by the colours red, blue, green. -/
def col3 (a b d : ℕ) : Colour → ℕ
  | red => a
  | blue => b
  | green => d

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- `R(1, ·, ·) - 1 = 0`: no nonempty set avoids a `K_1` in some colour. -/
theorem cap_of_one {κ : Type*} (c : V → V → κ) (s : κ → ℕ) (l : κ) (hl : s l = 1)
    (S : Finset V) (hS : AvoidsOn c s S) : S.card ≤ 0 := by
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · simp [h]
  · have := hS l {x} (singleton_subset_iff.mpr hx) (by simp [IsClique])
    rw [hl, card_singleton] at this
    exact absurd this (lt_irrefl _)

omit [Fintype V] in
/-- `R(2, 2, k) - 1 = k - 1`: a set with no red edge, no blue edge and no green `K_k`
is a green clique, so it has at most `k - 1` vertices. -/
theorem cap_two_two (c : V → V → Colour) (hc : ∀ x y, c x y = c y x) (k : ℕ) (S : Finset V)
    (hS : AvoidsOn c (col3 2 2 k) S) : S.card ≤ k - 1 := by
  have hgreen : IsClique c green S := by
    intro x hx y hy hxy
    have hsub : ({x, y} : Finset V) ⊆ S := insert_subset hx (singleton_subset_iff.mpr hy)
    cases h : c x y with
    | red =>
      have := hS red _ hsub ((isClique_pair c hc hxy).mpr h)
      rw [card_pair hxy] at this; exact absurd this (by simp [col3])
    | blue =>
      have := hS blue _ hsub ((isClique_pair c hc hxy).mpr h)
      rw [card_pair hxy] at this; exact absurd this (by simp [col3])
    | green => rfl
  have := hS green S (Subset.refl S) hgreen
  simp only [col3] at this
  omega

/-- For `t = (3, 3, k)`, `t - e_1 - e_2 = (2, 2, k)`. -/
theorem col3_sub_red_blue (k : ℕ) :
    col3 3 3 k - Pi.single red 1 - Pi.single blue 1 = col3 2 2 k := by
  funext l; cases l <;> rfl

/-- For `t = (3, 3, k)`, `t - e_1 - e_1 = (1, 3, k)`. -/
theorem col3_sub_red_red (k : ℕ) :
    col3 3 3 k - Pi.single red 1 - Pi.single red 1 = col3 1 3 k := by
  funext l; cases l <;> rfl

/-- Example of Lemma `lem:caps` with every cap hypothesis discharged: for `t = (3, 3, k)`,
`C_12 = R(2,2,k) - 1 = k - 1`, i.e. `|N_red(v) ∩ N_blue(u)| ≤ k - 1` for `u ∈ N_red(v)`
(compare `RamseyLocal.mixedNeighbourhood_card_le`). -/
theorem cap_C12_33k (c : V → V → Colour) (hc : ∀ x y, c x y = c y x) (k : ℕ)
    (hav : Avoids c (col3 3 3 k)) (v u : V) (hu : u ∈ nbhd c red v) :
    (nbhd c red v ∩ nbhd c blue u).card ≤ k - 1 :=
  local_caps_common c hc _ hav red blue (k - 1)
    (fun S hS => cap_two_two c hc k S (by rwa [col3_sub_red_blue] at hS)) v u hu

/-- Example: for `t = (3, 3, k)`, `C_11 = R(1,3,k) - 1 = 0`. -/
theorem cap_C11_33k (c : V → V → Colour) (hc : ∀ x y, c x y = c y x) (k : ℕ)
    (hav : Avoids c (col3 3 3 k)) (v u : V) (hu : u ∈ nbhd c red v) :
    (nbhd c red v ∩ nbhd c red u).card ≤ 0 :=
  local_caps_common c hc _ hav red red 0
    (fun S hS => cap_of_one c _ red (by rw [col3_sub_red_red]; rfl) S hS) v u hu

end ThreeColour


/-! ## Lemma `lem:corners`: corner identities -/

section Corners

variable {V κ : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]

omit [DecidableEq V] [DecidableEq κ] in
theorem mem_triangles {S : Finset V} : S ∈ (triangles : Finset (Finset V)) ↔ S.card = 3 := by
  simp [triangles, mem_powersetCard]

omit [Fintype V] [DecidableEq κ] in
theorem card_filter_triple {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (P : V → Prop) [DecidablePred P] :
    (({x, y, z} : Finset V).filter P).card =
      (if P x then 1 else 0) + (if P y then 1 else 0) + (if P z then 1 else 0) := by
  rw [card_filter, sum_insert (by simp [hxy, hxz]), sum_insert (by simp [hyz]), sum_singleton,
    add_assoc]

omit [Fintype V] in
theorem erase_triple_left {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) :
    ({x, y, z} : Finset V).erase x = {y, z} :=
  erase_insert (by simp [hxy, hxz])

omit [Fintype V] in
theorem erase_triple_mid {x y z : V} (hxy : x ≠ y) (hyz : y ≠ z) :
    ({x, y, z} : Finset V).erase y = {x, z} := by
  rw [erase_insert_of_ne hxy, erase_insert (by simp [hyz])]

omit [Fintype V] in
theorem erase_triple_right {x y z : V} (hxz : x ≠ z) (hyz : y ≠ z) :
    ({x, y, z} : Finset V).erase z = {x, y} := by
  rw [erase_insert_of_ne hxz, erase_insert_of_ne hyz, erase_singleton, insert_empty]

omit [Fintype V] [DecidableEq κ] in
theorem isClique_triple (c : V → V → κ) (hc : ∀ x y, c x y = c y x) {l : κ} {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    IsClique c l {x, y, z} ↔ c x y = l ∧ c x z = l ∧ c y z = l := by
  constructor
  · intro h
    exact ⟨h x (by simp) y (by simp) hxy, h x (by simp) z (by simp) hxz,
      h y (by simp) z (by simp) hyz⟩
  · rintro ⟨h1, h2, h3⟩ p hp q hq hpq
    simp only [mem_insert, mem_singleton] at hp hq
    have e1 := hc y x; have e2 := hc z x; have e3 := hc z y
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hpq
      | ((try simp only [e1, e2, e3]); assumption)

omit [Fintype V] [DecidableEq κ] in
theorem isRainbow_triple (c : V → V → κ) (hc : ∀ x y, c x y = c y x) {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    IsRainbow c {x, y, z} ↔ c x y ≠ c x z ∧ c x y ≠ c y z ∧ c x z ≠ c y z := by
  have e1 := hc y x; have e2 := hc z x; have e3 := hc z y
  constructor
  · intro h
    refine ⟨?_, h x (by simp) y (by simp) z (by simp) hxy hyz hxz, ?_⟩
    · have := h y (by simp) x (by simp) z (by simp) (Ne.symm hxy) hxz hyz
      rwa [e1] at this
    · have := h x (by simp) z (by simp) y (by simp) hxz (Ne.symm hyz) hxy
      rwa [e3] at this
  · rintro ⟨h1, h2, h3⟩ p hp q hq r hr hpq hqr hpr
    simp only [mem_insert, mem_singleton] at hp hq hr
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hpq
      | exact absurd rfl hqr
      | exact absurd rfl hpr
      | ((try simp only [e1, e2, e3])
         first
         | exact h1 | exact h2 | exact h3
         | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3)

omit [Fintype V] [DecidableEq κ] in
theorem isApex_triple (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (i j : κ) {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (IsApex c i j {x, y, z} x ↔ c x y = i ∧ c x z = i ∧ c y z = j) ∧
    (IsApex c i j {x, y, z} y ↔ c x y = i ∧ c y z = i ∧ c x z = j) ∧
    (IsApex c i j {x, y, z} z ↔ c x z = i ∧ c y z = i ∧ c x y = j) := by
  have e1 := hc y x; have e2 := hc z x; have e3 := hc z y
  refine ⟨?_, ?_, ?_⟩
  · rw [IsApex, erase_triple_left hxy hxz, isClique_pair c hc hyz]
    simp [and_assoc]
  · rw [IsApex, erase_triple_mid hxy hyz, isClique_pair c hc hxz]
    simp [e1, and_assoc]
  · rw [IsApex, erase_triple_right hxz hyz, isClique_pair c hc hxy]
    simp [e2, e3, and_assoc]

/-- Subsets of `N_i(v)` are the subsets of `V \ {v}` all of whose vertices are joined to `v`
in colour `i`. -/
theorem filter_powersetCard_nbhd (c : V → V → κ) (i : κ) (v : V) (k : ℕ)
    (P : Finset V → Prop) [DecidablePred P] :
    ((nbhd c i v).powersetCard k).filter P =
      ((univ.erase v).powersetCard k).filter (fun R => (∀ u ∈ R, c v u = i) ∧ P R) := by
  ext R
  simp only [mem_filter, mem_powersetCard, subset_iff, mem_nbhd, mem_erase, mem_univ, and_true]
  constructor
  · rintro ⟨⟨h, hk⟩, hP⟩
    exact ⟨⟨fun u hu => (h hu).1, hk⟩, fun u hu => (h hu).2, hP⟩
  · rintro ⟨⟨h, hk⟩, hc, hP⟩
    exact ⟨⟨fun u hu => ⟨h hu, hc u hu⟩, hk⟩, hP⟩

/-- `∑_v e_j(N_i(v))` counts pairs (triangle, `(i,j)`-apex of it). -/
theorem sum_e_nbhd_eq (c : V → V → κ) (i j : κ) :
    ∑ v, e c j (nbhd c i v) = ∑ S ∈ (triangles : Finset (Finset V)),
      (S.filter (IsApex c i j S)).card := by
  simp only [e, edgesIn, filter_powersetCard_nbhd]
  exact sum_pointed univ 2 (fun v R => (∀ u ∈ R, c v u = i) ∧ IsClique c j R)

/-- Lemma `lem:corners`, second identity: `3 M_i = ∑_v e_i(N_i(v))`. -/
theorem corner_mono (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (i : κ) :
    3 * M c i = ∑ v, e c i (nbhd c i v) := by
  rw [sum_e_nbhd_eq, M, card_eq_sum_ones, mul_sum, sum_filter]
  apply sum_congr rfl
  intro S hS
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp (mem_triangles.mp hS)
  obtain ⟨hax, hay, haz⟩ := isApex_triple c hc i i hxy hxz hyz
  rw [card_filter_triple hxy hxz hyz]
  simp only [hax, hay, haz, isClique_triple c hc hxy hxz hyz]
  by_cases h1 : c x y = i <;> by_cases h2 : c x z = i <;> by_cases h3 : c y z = i <;>
    simp [h1, h2, h3]

/-- For `i ≠ j` a triangle has at most one `(i,j)`-apex, so the number of its `(i,j)`-apexes is
`1` if it has type `T_{i,j}` and `0` otherwise. -/
theorem card_apex_eq (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (i j : κ) (hij : i ≠ j)
    (S : Finset V) (hS : S.card = 3) :
    (S.filter (IsApex c i j S)).card = if ∃ v ∈ S, IsApex c i j S v then 1 else 0 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp hS
  obtain ⟨hax, hay, haz⟩ := isApex_triple c hc i j hxy hxz hyz
  rw [card_filter_triple hxy hxz hyz]
  simp only [exists_mem_insert, mem_singleton, exists_eq_left, hax, hay, haz]
  clear hax hay haz hS
  generalize c x y = d, c x z = b, c y z = a
  by_cases h1 : d = i <;> by_cases h2 : b = i <;> by_cases h3 : a = i <;>
    by_cases h4 : d = j <;> by_cases h5 : b = j <;> by_cases h6 : a = j <;>
    simp_all

/-- Lemma `lem:corners`, fourth identity: `T_{i,j} = ∑_v e_j(N_i(v))` for `i ≠ j`. -/
theorem corner_apex (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (i j : κ) (hij : i ≠ j) :
    T c i j = ∑ v, e c j (nbhd c i v) := by
  rw [sum_e_nbhd_eq, T, card_eq_sum_ones, sum_filter]
  exact sum_congr rfl fun S hS =>
    (card_apex_eq c hc i j hij S (mem_triangles.mp hS)).symm

/-- Every 2-element vertex set is an edge of exactly one colour, so the `{i,i}`-corners at `v`
split by the colour of their third edge: `binom(d_i(v), 2) = ∑_l e_l(N_i(v))`. -/
theorem choose_two_deg [Fintype κ] (c : V → V → κ) (hc : ∀ x y, c x y = c y x)
    (i : κ) (v : V) :
    (deg c i v).choose 2 = ∑ l, e c l (nbhd c i v) := by
  simp only [e, edgesIn, deg]
  rw [← card_powersetCard]
  simp only [card_filter]
  rw [sum_comm, card_eq_sum_ones]
  apply sum_congr rfl
  intro R hR
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp (mem_powersetCard.mp hR).2
  simp only [isClique_pair c hc hxy]
  rw [sum_ite_eq]
  simp

/-- Lemma `lem:corners`, first identity: `∑_v binom(d_i(v), 2) = 3 M_i + ∑_{l ≠ i} T_{i,l}`. -/
theorem corner_choose [Fintype κ] (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (i : κ) :
    ∑ v, (deg c i v).choose 2 = 3 * M c i + ∑ l ∈ univ.erase i, T c i l := by
  simp only [choose_two_deg c hc i]
  rw [sum_comm, ← add_sum_erase _ _ (mem_univ i), corner_mono c hc i]
  congr 1
  apply sum_congr rfl
  intro l hl
  exact (corner_apex c hc i l (ne_of_mem_erase hl).symm).symm

end Corners

/-! ### The mixed corner identity (three colours) -/

section MixedCorners

open RamseyLocal (Colour)

variable {V κ : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]

omit [Fintype V] [DecidableEq κ] in
/-- `v` is the corner of an `{i,j}`-corner whose other two vertices form `R`. -/
theorem mixed_pair_iff (c : V → V → κ) (i j : κ) (v : V) {x y : V} :
    (∃ u ∈ ({x, y} : Finset V), ∃ w ∈ ({x, y} : Finset V), c v u = i ∧ c v w = j) ↔
      (c v x = i ∨ c v y = i) ∧ (c v x = j ∨ c v y = j) := by
  simp only [exists_mem_insert, mem_singleton, exists_eq_left]
  tauto

/-- The `{i,j}`-corners at `v` (`i ≠ j`), counted as 2-sets `R ⊆ V \ {v}` with one vertex of `R`
joined to `v` in colour `i` and the other in colour `j`: there are `d_i(v) d_j(v)` of them. -/
theorem deg_mul_deg (c : V → V → κ) (i j : κ) (hij : i ≠ j) (v : V) :
    deg c i v * deg c j v =
      (((univ.erase v).powersetCard 2).filter
        fun R => ∃ u ∈ R, ∃ w ∈ R, c v u = i ∧ c v w = j).card := by
  rw [deg, deg, ← card_product]
  refine card_bij (fun p _ => {p.1, p.2}) ?_ ?_ ?_
  · rintro ⟨u, w⟩ hp
    simp only [mem_product, mem_nbhd] at hp
    obtain ⟨⟨hu, hcu⟩, hw, hcw⟩ := hp
    have huw : u ≠ w := by rintro rfl; exact hij (hcu.symm.trans hcw)
    simp only [mem_filter, mem_powersetCard]
    refine ⟨⟨?_, card_pair huw⟩, u, by simp, w, by simp, hcu, hcw⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  · rintro ⟨u, w⟩ hp ⟨u', w'⟩ hp' heq
    dsimp only at heq
    simp only [mem_product, mem_nbhd] at hp hp'
    have hu : u ∈ ({u', w'} : Finset V) := by rw [← heq]; simp
    have hw : w ∈ ({u', w'} : Finset V) := by rw [← heq]; simp
    simp only [mem_insert, mem_singleton] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl <;> simp_all
  · intro R hR
    simp only [mem_filter, mem_powersetCard] at hR
    obtain ⟨⟨hRsub, hRcard⟩, u, hu, w, hw, hcu, hcw⟩ := hR
    have huw : u ≠ w := by rintro rfl; exact hij (hcu.symm.trans hcw)
    refine ⟨(u, w), ?_, ?_⟩
    · simp only [mem_product, mem_nbhd]
      exact ⟨⟨(mem_erase.mp (hRsub hu)).1, hcu⟩, (mem_erase.mp (hRsub hw)).1, hcw⟩
    · refine eq_of_subset_of_card_le ?_ (by rw [hRcard, card_pair huw])
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption

/-- The finite colour-pattern identity behind the mixed corner identity: for a triangle with
edge colours `d = c x y`, `b = c x z`, `a = c y z` and colours `i ≠ j`, the number of its
vertices carrying an `{i,j}`-corner is `2[type T_{i,j}] + 2[type T_{j,i}] + [rainbow]`. -/
theorem mixed_pattern (a b d i j : Colour) (hij : i ≠ j) :
    ((if (d = i ∨ b = i) ∧ (d = j ∨ b = j) then 1 else 0) +
      (if (d = i ∨ a = i) ∧ (d = j ∨ a = j) then 1 else 0) +
      (if (b = i ∨ a = i) ∧ (b = j ∨ a = j) then 1 else 0) : ℕ) =
    2 * (if (d = i ∧ b = i ∧ a = j) ∨ (d = i ∧ a = i ∧ b = j) ∨ (b = i ∧ a = i ∧ d = j)
      then 1 else 0) +
    2 * (if (d = j ∧ b = j ∧ a = i) ∨ (d = j ∧ a = j ∧ b = i) ∨ (b = j ∧ a = j ∧ d = i)
      then 1 else 0) +
    (if d ≠ b ∧ d ≠ a ∧ b ≠ a then 1 else 0) := by
  cases a <;> cases b <;> cases d <;> cases i <;> cases j <;>
    first | exact absurd rfl hij | decide

/-- Lemma `lem:corners`, third identity: `∑_v d_i(v) d_j(v) = 2 T_{i,j} + 2 T_{j,i} + X`
for colours `i ≠ j` of a 3-colouring. -/
theorem corner_mixed (c : V → V → Colour) (hc : ∀ x y, c x y = c y x) (i j : Colour)
    (hij : i ≠ j) :
    ∑ v, deg c i v * deg c j v = 2 * T c i j + 2 * T c j i + X c := by
  simp only [deg_mul_deg c i j hij]
  rw [sum_pointed univ 2 (fun v R => ∃ u ∈ R, ∃ w ∈ R, c v u = i ∧ c v w = j)]
  rw [T, T, X, card_eq_sum_ones, card_eq_sum_ones, card_eq_sum_ones, sum_filter, sum_filter,
    sum_filter, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro S hS
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp (mem_powersetCard.mp hS).2
  obtain ⟨hax, hay, haz⟩ := isApex_triple c hc i j hxy hxz hyz
  obtain ⟨hbx, hby, hbz⟩ := isApex_triple c hc j i hxy hxz hyz
  rw [card_filter_triple hxy hxz hyz, erase_triple_left hxy hxz, erase_triple_mid hxy hyz,
    erase_triple_right hxz hyz]
  simp only [mixed_pair_iff]
  simp only [exists_mem_insert, mem_singleton, exists_eq_left, hax, hay, haz,
    hbx, hby, hbz, isRainbow_triple c hc hxy hxz hyz, hc y x, hc z x, hc z y]
  clear hax hay haz hbx hby hbz hS
  generalize c x y = d, c x z = b, c y z = a
  exact mixed_pattern a b d i j hij

/-- Lemma `lem:corners` (corner identities), all four, for every 3-colouring of `K_V`. -/
theorem corner_identities (c : V → V → Colour) (hc : ∀ x y, c x y = c y x) :
    (∀ i, ∑ v, (deg c i v).choose 2 = 3 * M c i + ∑ l ∈ univ.erase i, T c i l) ∧
    (∀ i, 3 * M c i = ∑ v, e c i (nbhd c i v)) ∧
    (∀ i j, i ≠ j → ∑ v, deg c i v * deg c j v = 2 * T c i j + 2 * T c j i + X c) ∧
    (∀ i j, i ≠ j → T c i j = ∑ v, e c j (nbhd c i v)) :=
  ⟨corner_choose c hc, corner_mono c hc, corner_mixed c hc, corner_apex c hc⟩

end MixedCorners

/-! ## Bridge to the `RamseyLocal` conventions for `t = (3, 3, k)` -/

section Bridge33k

open RamseyLocal (Colour)
open RamseyLocal.Colour

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A colour-`l` clique on at least three vertices contains an ordered colour-`l` triangle. -/
theorem card_lt_three_of_noMono (c : V → V → Colour) (l : Colour)
    (hl : RamseyLocal.NoMonoTriangle c l) (K : Finset V) (hK : IsClique c l K) :
    K.card < 3 := by
  by_contra hn
  obtain ⟨T, hTK, hT⟩ := exists_subset_card_eq (Nat.le_of_not_gt hn)
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp hT
  have hx : x ∈ K := hTK (by simp)
  have hy : y ∈ K := hTK (by simp)
  have hz : z ∈ K := hTK (by simp)
  exact hl x y z (hK x hx y hy hxy) (hK x hx z hz hxz) (hK y hy z hz hyz)

/-- Bridge to the conventions of `RamseyLocal` (`LocalCombinatorics.lean`): for a symmetric
colouring with green diagonal, being `(3,3,k)`-avoiding is the same as having no red and no
blue (ordered) triangle and no green clique on `k` vertices. -/
theorem avoids_33k_iff (c : V → V → Colour) (hc : ∀ x y, c x y = c y x)
    (hdiag : ∀ v, c v v = green) (k : ℕ) :
    Avoids c (col3 3 3 k) ↔
      RamseyLocal.NoMonoTriangle c red ∧ RamseyLocal.NoMonoTriangle c blue ∧
        RamseyLocal.AvoidsGreenK c k := by
  have hne : ∀ {l : Colour}, l ≠ green → ∀ {x y : V}, c x y = l → x ≠ y := by
    rintro l hl x y h rfl; exact hl (h.symm.trans (hdiag x))
  have hmono : ∀ l : Colour, l ≠ green → Avoids c (col3 3 3 k) →
      RamseyLocal.NoMonoTriangle c l := by
    intro l hl hav v x y hvx hvy hxy
    have hcl := (isClique_triple c hc (hne hl hvx) (hne hl hvy) (hne hl hxy)).mpr ⟨hvx, hvy, hxy⟩
    have h3 := hav l _ (subset_univ _) hcl
    rw [card_eq_three.mpr ⟨v, x, y, hne hl hvx, hne hl hvy, hne hl hxy, rfl⟩] at h3
    cases l <;> simp_all [col3]
  constructor
  · intro hav
    exact ⟨hmono red (by decide) hav, hmono blue (by decide) hav,
      fun S hS => hav green S (subset_univ S) hS⟩
  · rintro ⟨hr, hb, hg⟩ l K _ hK
    cases l
    · exact card_lt_three_of_noMono c red hr K hK
    · exact card_lt_three_of_noMono c blue hb K hK
    · exact hg K hK

end Bridge33k

/-! ## Additions from the audit: the paper's constants `R(·) - 1`, the remark that Lemma
`lem:caps` is the case `|Y| ≤ 2` of Lemma `lem:multicaps`, and the examples `C_21`, `C_22` -/

section RamseyForm

variable {V κ : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]

/-- Lemma `lem:caps`, first part, with the paper's constant: `d_i(v) ≤ R(t - e_i) - 1`
(given that `R(t - e_i)` exists). -/
theorem local_caps_degree_R (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (t : κ → ℕ)
    (hav : Avoids c t) (i : κ) (hex : ∃ n, RamseyLE κ (t - Pi.single i 1) n) (v : V) :
    deg c i v ≤ ramseyNumber κ (t - Pi.single i 1) - 1 :=
  local_caps_degree c hc t hav i _ (fun S hS => cap_of_ramseyNumber hex c hc S hS) v

/-- Lemma `lem:caps`, second part, with the paper's constant:
`|N_i(v) ∩ N_j(u)| ≤ R(t - e_i - e_j) - 1` for `u ∈ N_i(v)`. -/
theorem local_caps_common_R (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (t : κ → ℕ)
    (hav : Avoids c t) (i j : κ)
    (hex : ∃ n, RamseyLE κ (t - Pi.single i 1 - Pi.single j 1) n)
    (v u : V) (hu : u ∈ nbhd c i v) :
    (nbhd c i v ∩ nbhd c j u).card ≤ ramseyNumber κ (t - Pi.single i 1 - Pi.single j 1) - 1 :=
  local_caps_common c hc t hav i j _ (fun S hS => cap_of_ramseyNumber hex c hc S hS) v u hu

/-- Corollary `cor:handshake` with the paper's constant `C_ij = R(t - e_i - e_j) - 1`. -/
theorem handshake_cap_R (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (t : κ → ℕ)
    (hav : Avoids c t) (i j : κ)
    (hex : ∃ n, RamseyLE κ (t - Pi.single i 1 - Pi.single j 1) n) (v : V) :
    e c j (nbhd c i v) ≤
      (ramseyNumber κ (t - Pi.single i 1 - Pi.single j 1) - 1) * deg c i v / 2 :=
  handshake_cap c hc t hav i j _ (fun S hS => cap_of_ramseyNumber hex c hc S hS) v

/-- Lemma `lem:multicaps` with the paper's constant: `|⋂_{y∈Y} N_{a(y)}(y)| ≤ R(t - w) - 1`. -/
theorem multicaps_R (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (t : κ → ℕ)
    (hav : Avoids c t) (Y : Finset V) (a : V → κ)
    (hex : ∃ n, RamseyLE κ (t - fun l => maxCliqueOrder c l (colourClass Y a l)) n) :
    (commonNbhd c Y a).card ≤
      ramseyNumber κ (t - fun l => maxCliqueOrder c l (colourClass Y a l)) - 1 :=
  multicaps c hc t hav Y a _ (fun S hS => cap_of_ramseyNumber hex c hc S hS)

end RamseyForm

section SmallY

variable {V κ : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]

omit [Fintype V] in
/-- The largest colour-`l` clique inside a colour-`l` clique `A` is `A` itself. -/
theorem maxCliqueOrder_of_isClique (c : V → V → κ) (l : κ) (A : Finset V)
    (hA : IsClique c l A) : maxCliqueOrder c l A = A.card := by
  apply le_antisymm
  · exact Finset.sup_le fun K hK => card_le_card (mem_powerset.mp (mem_filter.mp hK).1)
  · exact le_sup (f := card) (mem_filter.mpr ⟨mem_powerset_self A, hA⟩)

/-- The remark after Lemma `lem:multicaps`, first case: `Y = {v}` with `a(v) = i` gives
`w = e_i`, so `lem:multicaps` yields the cap `D_i` of Lemma `lem:caps`. -/
theorem multicaps_singleton (c : V → V → κ) (i : κ) (v : V) :
    commonNbhd c {v} (fun _ => i) = nbhd c i v ∧
    (fun l => maxCliqueOrder c l (colourClass {v} (fun _ => i) l)) = Pi.single i 1 := by
  constructor
  · ext x; simp [commonNbhd]
  · funext l
    by_cases hl : l = i
    · subst hl
      rw [maxCliqueOrder_of_isClique]
      · simp [colourClass]
      · intro x hx y hy hxy
        simp [colourClass] at hx hy; exact absurd (hx.trans hy.symm) hxy
    · rw [maxCliqueOrder_of_isClique]
      · simp [colourClass, Ne.symm hl, hl]
      · intro x hx; simp [colourClass, Ne.symm hl] at hx

/-- The remark after Lemma `lem:multicaps`, second case: for `Y = {v, u}` with `u ∈ N_i(v)`,
`a(v) = i` and `a(u) = j`, the common neighbourhood is `N_i(v) ∩ N_j(u)` and
`t - w = t - e_i - e_j` (both when `j ≠ i`, where `w = e_i + e_j`, and when `j = i`, where
`w = 2 e_i` because `uv` has colour `i`). So `lem:multicaps` yields the cap `C_ij`. -/
theorem multicaps_pair (c : V → V → κ) (hc : ∀ x y, c x y = c y x) (i j : κ) (t : κ → ℕ)
    (v u : V) (hu : u ∈ nbhd c i v) :
    let a : V → κ := fun x => if x = v then i else j
    commonNbhd c {v, u} a = nbhd c i v ∩ nbhd c j u ∧
    (t - fun l => maxCliqueOrder c l (colourClass {v, u} a l)) =
      t - Pi.single i 1 - Pi.single j 1 := by
  intro a
  obtain ⟨huv, hvu⟩ := mem_nbhd.mp hu
  have hau : a u = j := by simp [a, huv]
  have hav : a v = i := by simp [a]
  constructor
  · ext x; simp [commonNbhd, hau, hav]
  · funext l
    have hcl : IsClique c l (colourClass {v, u} a l) := by
      intro x hx y hy hxy
      simp only [colourClass, mem_filter, mem_insert, mem_singleton] at hx hy
      rcases hx with ⟨rfl | rfl, hx⟩ <;> rcases hy with ⟨rfl | rfl, hy⟩
      · exact absurd rfl hxy
      · rw [hvu, ← hx, hav]
      · rw [hc, hvu, ← hy, hav]
      · exact absurd rfl hxy
    rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, maxCliqueOrder_of_isClique c l _ hcl,
      Nat.sub_sub]
    congr 1
    have : colourClass {v, u} a l =
        (if l = i then {v} else ∅) ∪ (if l = j then {u} else ∅) := by
      ext x
      simp only [colourClass, mem_filter, mem_insert, mem_singleton, mem_union]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · left; rw [if_pos (hav ▸ hx).symm]; simp
        · right; rw [if_pos (hau ▸ hx).symm]; simp
      · intro h
        rcases h with h | h <;> split_ifs at h with hl <;> simp at h <;> subst h
        · exact ⟨Or.inl rfl, hav.trans hl.symm⟩
        · exact ⟨Or.inr rfl, hau.trans hl.symm⟩
    rw [this, card_union_of_disjoint]
    · simp only [Pi.single_apply]
      split_ifs <;> simp
    · rw [disjoint_iff_ne]
      intro x hx y hy
      split_ifs at hx hy <;> simp at hx hy
      subst hx hy; exact Ne.symm huv

/-- Lemma `lem:caps`, first part, derived from Lemma `lem:multicaps` with `Y = {v}`. -/
theorem local_caps_degree_via_multicaps (c : V → V → κ) (hc : ∀ x y, c x y = c y x)
    (t : κ → ℕ) (hav : Avoids c t) (i : κ) (D : ℕ)
    (hD : ∀ S : Finset V, AvoidsOn c (t - Pi.single i 1) S → S.card ≤ D) (v : V) :
    deg c i v ≤ D := by
  obtain ⟨h1, h2⟩ := multicaps_singleton c i v
  have h := multicaps c hc t hav {v} (fun _ => i) D (by rw [h2]; exact hD)
  rwa [h1] at h

/-- Lemma `lem:caps`, second part, derived from Lemma `lem:multicaps` with `Y = {v, u}`. -/
theorem local_caps_common_via_multicaps (c : V → V → κ) (hc : ∀ x y, c x y = c y x)
    (t : κ → ℕ) (hav : Avoids c t) (i j : κ) (C : ℕ)
    (hC : ∀ S : Finset V, AvoidsOn c (t - Pi.single i 1 - Pi.single j 1) S → S.card ≤ C)
    (v u : V) (hu : u ∈ nbhd c i v) :
    (nbhd c i v ∩ nbhd c j u).card ≤ C := by
  obtain ⟨h1, h2⟩ := multicaps_pair c hc i j t v u hu
  have h := multicaps c hc t hav {v, u} (fun x => if x = v then i else j) C
    (by rw [h2]; exact hC)
  rwa [h1] at h

end SmallY

section More33k

open RamseyLocal (Colour)
open RamseyLocal.Colour

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For `t = (3, 3, k)`, `t - e_2 - e_1 = (2, 2, k)`. -/
theorem col3_sub_blue_red (k : ℕ) :
    col3 3 3 k - Pi.single blue 1 - Pi.single red 1 = col3 2 2 k := by
  funext l; cases l <;> rfl

/-- For `t = (3, 3, k)`, `t - e_2 - e_2 = (3, 1, k)`. -/
theorem col3_sub_blue_blue (k : ℕ) :
    col3 3 3 k - Pi.single blue 1 - Pi.single blue 1 = col3 3 1 k := by
  funext l; cases l <;> rfl

/-- Example: for `t = (3, 3, k)`, `C_21 = R(2,2,k) - 1 = k - 1`. -/
theorem cap_C21_33k (c : V → V → Colour) (hc : ∀ x y, c x y = c y x) (k : ℕ)
    (hav : Avoids c (col3 3 3 k)) (v u : V) (hu : u ∈ nbhd c blue v) :
    (nbhd c blue v ∩ nbhd c red u).card ≤ k - 1 :=
  local_caps_common c hc _ hav blue red (k - 1)
    (fun S hS => cap_two_two c hc k S (by rwa [col3_sub_blue_red] at hS)) v u hu

/-- Example: for `t = (3, 3, k)`, `C_22 = R(3,1,k) - 1 = 0`. -/
theorem cap_C22_33k (c : V → V → Colour) (hc : ∀ x y, c x y = c y x) (k : ℕ)
    (hav : Avoids c (col3 3 3 k)) (v u : V) (hu : u ∈ nbhd c blue v) :
    (nbhd c blue v ∩ nbhd c blue u).card ≤ 0 :=
  local_caps_common c hc _ hav blue blue 0
    (fun S hS => cap_of_one c _ blue (by rw [col3_sub_blue_blue]; rfl) S hS) v u hu

end More33k

#print axioms local_caps
#print axioms local_caps_degree
#print axioms local_caps_common
#print axioms handshake
#print axioms handshake_cap
#print axioms multicaps
#print axioms multicaps_of_cliques
#print axioms cap_of_ramseyLE
#print axioms cap_of_ramseyNumber
#print axioms avoidsOn_iff_no_exact
#print axioms cap_two_two
#print axioms cap_C12_33k
#print axioms cap_C11_33k
#print axioms avoids_33k_iff
#print axioms corner_choose
#print axioms corner_mono
#print axioms corner_mixed
#print axioms corner_apex
#print axioms card_apex_eq
#print axioms corner_identities
#print axioms local_caps_degree_R
#print axioms local_caps_common_R
#print axioms handshake_cap_R
#print axioms multicaps_R
#print axioms multicaps_singleton
#print axioms multicaps_pair
#print axioms local_caps_degree_via_multicaps
#print axioms local_caps_common_via_multicaps
#print axioms cap_C21_33k
#print axioms cap_C22_33k


end RamseyLean.Caps
