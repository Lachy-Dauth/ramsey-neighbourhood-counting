import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Local combinatorial ingredients of the three-colour Ramsey argument

This file formalizes the actual edge-colouring argument underlying the
triangle bound, not an assumption of the final Ramsey inequality.

`NoMonoTriangle` forbids monochromatic ordered triangles. For a colouring
whose diagonal is green, this agrees with the usual red/blue triangle-free
condition, since repeated vertices cannot make red/blue triangles.

`AvoidsGreenK` says every green clique has fewer than `k` vertices. This is
an explicit graph hypothesis, not an imported assertion about Ramsey numbers.
-/

namespace RamseyLocal

inductive Colour where
  | red | blue | green
  deriving DecidableEq

open Colour

variable {V : Type*}

def NoMonoTriangle (c : V → V → Colour) (a : Colour) : Prop :=
  ∀ v x y, c v x = a → c v y = a → c x y = a → False

def GreenClique (c : V → V → Colour) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c x y = green

def AvoidsGreenK (c : V → V → Colour) (k : ℕ) : Prop :=
  ∀ S : Finset V, GreenClique c S → S.card < k

/-- The blue neighbours of `u` inside the red neighbourhood of `v`
    form a green clique: each other colour would create a forbidden triangle. -/
theorem mixed_common_green (c : V → V → Colour)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue)
    (v u x y : V)
    (hvx : c v x = red) (hvy : c v y = red)
    (hux : c u x = blue) (huy : c u y = blue) :
    c x y = green := by
  cases hxy : c x y with
  | red => exact False.elim (hred v x y hvx hvy hxy)
  | blue => exact False.elim (hblue u x y hux huy hxy)
  | green => rfl

/-- The corresponding statement after interchanging red and blue. -/
theorem mixed_common_green_swap (c : V → V → Colour)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue)
    (v u x y : V)
    (hvx : c v x = blue) (hvy : c v y = blue)
    (hux : c u x = red) (huy : c u y = red) :
    c x y = green := by
  cases hxy : c x y with
  | red => exact False.elim (hred u x y hux huy hxy)
  | blue => exact False.elim (hblue v x y hvx hvy hxy)
  | green => rfl

variable [Fintype V] [DecidableEq V]

def mixedNeighbourhood (c : V → V → Colour) (v u : V) : Finset V :=
  Finset.univ.filter fun w => c v w = red ∧ c u w = blue

def mixedNeighbourhoodSwap (c : V → V → Colour) (v u : V) : Finset V :=
  Finset.univ.filter fun w => c v w = blue ∧ c u w = red

def neighbourhood (c : V → V → Colour) (a : Colour) (v : V) : Finset V :=
  Finset.univ.filter fun w => c v w = a

theorem mixedNeighbourhood_is_green (c : V → V → Colour)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue)
    (v u : V) : GreenClique c (mixedNeighbourhood c v u) := by
  intro x hx y hy _
  obtain ⟨hvx, hux⟩ := (Finset.mem_filter.mp hx).2
  obtain ⟨hvy, huy⟩ := (Finset.mem_filter.mp hy).2
  exact mixed_common_green c hred hblue v u x y hvx hvy hux huy

theorem mixedNeighbourhoodSwap_is_green (c : V → V → Colour)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue)
    (v u : V) : GreenClique c (mixedNeighbourhoodSwap c v u) := by
  intro x hx y hy _
  obtain ⟨hvx, hux⟩ := (Finset.mem_filter.mp hx).2
  obtain ⟨hvy, huy⟩ := (Finset.mem_filter.mp hy).2
  exact mixed_common_green_swap c hred hblue v u x y hvx hvy hux huy

theorem mixedNeighbourhood_card_le (c : V → V → Colour) (k : ℕ)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue)
    (hgreen : AvoidsGreenK c k) (v u : V) :
    (mixedNeighbourhood c v u).card ≤ k - 1 := by
  have h := hgreen _ (mixedNeighbourhood_is_green c hred hblue v u)
  omega

theorem mixedNeighbourhoodSwap_card_le (c : V → V → Colour) (k : ℕ)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue)
    (hgreen : AvoidsGreenK c k) (v u : V) :
    (mixedNeighbourhoodSwap c v u).card ≤ k - 1 := by
  have h := hgreen _ (mixedNeighbourhoodSwap_is_green c hred hblue v u)
  omega

def colourIndicator (c : V → V → Colour) (a : Colour) (v w : V) : ℕ :=
  if c v w = a then 1 else 0

theorem mixed_indicator_sum_eq_card (c : V → V → Colour) (v u : V) :
    (∑ w : V, colourIndicator c red v w * colourIndicator c blue u w) =
      (mixedNeighbourhood c v u).card := by
  have hpoint (w : V) :
      colourIndicator c red v w * colourIndicator c blue u w =
        if c v w = red ∧ c u w = blue then 1 else 0 := by
    by_cases hr : c v w = red <;> by_cases hb : c u w = blue <;>
      simp [colourIndicator, hr, hb]
  simp_rw [hpoint]
  simp [mixedNeighbourhood]

/-- Matrix-style version of the local common-neighbour bound. -/
theorem mixed_indicator_sum_le (c : V → V → Colour) (k : ℕ)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue)
    (hgreen : AvoidsGreenK c k) (v u : V) :
    (∑ w : V, colourIndicator c red v w * colourIndicator c blue u w) ≤ k - 1 := by
  rw [mixed_indicator_sum_eq_card]
  exact mixedNeighbourhood_card_le c k hred hblue hgreen v u

theorem mixed_indicator_sum_eq_card_swap (c : V → V → Colour) (v u : V) :
    (∑ w : V, colourIndicator c blue v w * colourIndicator c red u w) =
      (mixedNeighbourhoodSwap c v u).card := by
  have hpoint (w : V) :
      colourIndicator c blue v w * colourIndicator c red u w =
        if c v w = blue ∧ c u w = red then 1 else 0 := by
    by_cases hb : c v w = blue <;> by_cases hr : c u w = red <;>
      simp [colourIndicator, hr, hb]
  simp_rw [hpoint]
  simp [mixedNeighbourhoodSwap]

theorem mixed_indicator_sum_le_swap (c : V → V → Colour) (k : ℕ)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue)
    (hgreen : AvoidsGreenK c k) (v u : V) :
    (∑ w : V, colourIndicator c blue v w * colourIndicator c red u w) ≤ k - 1 := by
  rw [mixed_indicator_sum_eq_card_swap]
  exact mixedNeighbourhoodSwap_card_le c k hred hblue hgreen v u

/-- Integral versions use the cast of natural subtraction, so no positivity
hypothesis on `k` is hidden in a coercion. -/
theorem mixed_indicator_sum_le_int (c : V → V → Colour) (k : ℕ)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue)
    (hgreen : AvoidsGreenK c k) (v u : V) :
    (∑ w : V, (colourIndicator c red v w : ℤ) * (colourIndicator c blue u w : ℤ)) ≤
      ((k - 1 : ℕ) : ℤ) := by
  exact_mod_cast mixed_indicator_sum_le c k hred hblue hgreen v u

theorem mixed_indicator_sum_le_int_swap (c : V → V → Colour) (k : ℕ)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue)
    (hgreen : AvoidsGreenK c k) (v u : V) :
    (∑ w : V, (colourIndicator c blue v w : ℤ) * (colourIndicator c red u w : ℤ)) ≤
      ((k - 1 : ℕ) : ℤ) := by
  exact_mod_cast mixed_indicator_sum_le_swap c k hred hblue hgreen v u

/-- The ordered blue-edge count in a red neighbourhood is at most
    `(k-1)` times the red degree. Each unordered blue edge is counted twice. -/
theorem local_ordered_edge_bound (c : V → V → Colour) (k : ℕ)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue)
    (hgreen : AvoidsGreenK c k) (v : V) :
    (∑ u ∈ neighbourhood c red v, (mixedNeighbourhood c v u).card) ≤
      (neighbourhood c red v).card * (k - 1) := by
  calc
    _ ≤ ∑ _u ∈ neighbourhood c red v, (k - 1) := by
      apply Finset.sum_le_sum
      intro u _
      exact mixedNeighbourhood_card_le c k hred hblue hgreen v u
    _ = _ := by simp

theorem local_ordered_edge_bound_swap (c : V → V → Colour) (k : ℕ)
    (hred : NoMonoTriangle c red) (hblue : NoMonoTriangle c blue)
    (hgreen : AvoidsGreenK c k) (v : V) :
    (∑ u ∈ neighbourhood c blue v, (mixedNeighbourhoodSwap c v u).card) ≤
      (neighbourhood c blue v).card * (k - 1) := by
  calc
    _ ≤ ∑ _u ∈ neighbourhood c blue v, (k - 1) := by
      apply Finset.sum_le_sum
      intro u _
      exact mixedNeighbourhoodSwap_card_le c k hred hblue hgreen v u
    _ = _ := by simp

/-- A boolean indicator, used only in the finite colour-pattern identity. -/
def isH : Colour → ℕ
  | red => 1 | blue => 1 | green => 0

def repeatedApex : Colour → Colour → Colour → ℕ
  | red, red, blue => 1
  | blue, blue, red => 1
  | _, _, _ => 0

/-- In an H-triangle with no monochromatic red or blue triangle, exactly
one vertex is incident to the repeated colour. This is the pointwise
identity that justifies counting triangles at their unique apex. -/
theorem unique_repeated_apex (a b d : Colour)
    (hnr : ¬ (a = red ∧ b = red ∧ d = red))
    (hnb : ¬ (a = blue ∧ b = blue ∧ d = blue)) :
    isH a * isH b * isH d =
      repeatedApex a b d + repeatedApex a d b + repeatedApex b d a := by
  cases a <;> cases b <;> cases d <;>
    simp_all [isH, repeatedApex]

#print axioms mixed_common_green
#print axioms mixedNeighbourhood_card_le
#print axioms local_ordered_edge_bound
#print axioms unique_repeated_apex

end RamseyLocal
