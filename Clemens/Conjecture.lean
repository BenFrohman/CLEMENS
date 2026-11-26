/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

namespace Clemens

def h0SplitBundle (a b : ℤ) : ℕ := Int.toNat (a + 1) + Int.toNat (b + 1)

theorem balanced_normal_bundle_rigid : h0SplitBundle (-1) (-1) = 0 := by
  unfold h0SplitBundle
  decide

structure GeneralQuinticThreefold where
  IsFiniteSet : ℕ → Prop

class ClemensResolvedLowDegree (X : GeneralQuinticThreefold) : Prop where
  resolved_le_11 : ∀ d : ℕ, 1 ≤ d → d ≤ 11 → X.IsFiniteSet d
  resolved_smooth_12 : X.IsFiniteSet 12

class ClemensOpenFrontier (X : GeneralQuinticThreefold) : Prop where
  open_singular_12 : X.IsFiniteSet 12
  open_ge_13 : ∀ d : ℕ, 13 ≤ d → X.IsFiniteSet d

theorem clemens_finiteness_from_frontier
    (X : GeneralQuinticThreefold)
    [hLow : ClemensResolvedLowDegree X]
    [hOpen : ClemensOpenFrontier X] :
    ∀ d : ℕ, 1 ≤ d → X.IsFiniteSet d := by
  intro d hd1
  by_cases h11 : d ≤ 11
  · exact hLow.resolved_le_11 d hd1 h11
  · by_cases h12 : d = 12
    · subst h12
      exact hOpen.open_singular_12
    · exact hOpen.open_ge_13 d (by omega)

end Clemens
