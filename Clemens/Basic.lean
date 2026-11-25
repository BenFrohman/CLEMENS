/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

/-!
# Conditional reduction for the Clemens conjecture

Records the known range and isolates the open birational tail.
Does not prove the conjecture.
-/

namespace ClemensConjecture

/-- Propositional interface recording the known finiteness results. -/
structure QuinticThreefoldClemensData where
  ClemensAt : ℕ → Prop
  SmoothClemensAt : ℕ → Prop
  SingularClemensAt : ℕ → Prop
  clemens_iff_smooth_and_singular :
    ∀ d, ClemensAt d ↔ SmoothClemensAt d ∧ SingularClemensAt d
  cotterill_le_11 : ∀ d, 1 ≤ d → d ≤ 11 → ClemensAt d
  ballico_fontanari_12 : SmoothClemensAt 12

/-- The full conjecture is equivalent to the singular degree-12 case
    together with the tail d ≥ 13. -/
theorem clemens_iff_singular12_and_ge13 (Q : QuinticThreefoldClemensData) :
    (∀ d, 1 ≤ d → Q.ClemensAt d) ↔
      Q.SingularClemensAt 12 ∧ (∀ d, 13 ≤ d → Q.ClemensAt d) := by
  constructor
  · intro hall
    refine ⟨?_, fun d hd => hall d (by omega)⟩
    exact ((Q.clemens_iff_smooth_and_singular 12).mp (hall 12 (by omega))).2
  · rintro ⟨hsing12, hge13⟩ d hd1
    by_cases h11 : d ≤ 11
    · exact Q.cotterill_le_11 d hd1 h11
    · by_cases h12 : d = 12
      · subst h12
        exact (Q.clemens_iff_smooth_and_singular 12).mpr ⟨Q.ballico_fontanari_12, hsing12⟩
      · exact hge13 d (by omega)

end ClemensConjecture
