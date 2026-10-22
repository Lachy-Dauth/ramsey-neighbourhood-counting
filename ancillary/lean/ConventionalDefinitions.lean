import LocalCombinatorics

/-!
This file bridges the local formalization's convenient hypotheses to the
usual graph-theoretic conventions: forbidden triangles have three distinct
vertices, and a forbidden green clique has exactly `k` vertices.
-/

namespace RamseyLocal
open Colour
variable {V : Type*}

/-- With a green diagonal, a red or blue edge cannot be a loop. -/
theorem distinct_of_nongreen_edge (c : V → V → Colour)
    (hdiag : ∀ v, c v v = green) {a : Colour} (ha : a ≠ green)
    {v w : V} (hedge : c v w = a) : v ≠ w := by
  intro heq
  subst w
  exact ha (hedge.symm.trans (hdiag v))

/-- The ordered triangle convention does not strengthen the ordinary
    distinct-vertex condition for red or blue. -/
theorem noMonoTriangle_of_distinct (c : V → V → Colour)
    (hdiag : ∀ v, c v v = green) {a : Colour} (ha : a ≠ green)
    (htri : ∀ v x y, v ≠ x → v ≠ y → x ≠ y →
      c v x = a → c v y = a → c x y = a → False) :
    NoMonoTriangle c a := by
  intro v x y hvx hvy hxy
  exact htri v x y
    (distinct_of_nongreen_edge c hdiag ha hvx)
    (distinct_of_nongreen_edge c hdiag ha hvy)
    (distinct_of_nongreen_edge c hdiag ha hxy) hvx hvy hxy

/-- A large clique has a clique subset of exactly the forbidden size, so
    forbidding exact size `k` is equivalent to bounding every clique. -/
theorem avoidsGreenK_iff_no_exact (c : V → V → Colour) (k : ℕ) :
    AvoidsGreenK c k ↔ ∀ S : Finset V, S.card = k → ¬ GreenClique c S := by
  constructor
  · intro havoid S hcard hclique
    have h := havoid S hclique
    omega
  · intro hexact S hclique
    by_contra hn
    have hle : k ≤ S.card := Nat.le_of_not_gt hn
    obtain ⟨T, hsub, hcard⟩ := Finset.exists_subset_card_eq hle
    apply hexact T hcard
    intro x hx y hy hxy
    exact hclique x (hsub hx) y (hsub hy) hxy

#print axioms noMonoTriangle_of_distinct
#print axioms avoidsGreenK_iff_no_exact
end RamseyLocal
