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

structure QuinticThreefoldClemensData where
  ClemensAtDegree : ℕ → Prop
  SmoothClemensAtDegree : ℕ → Prop
  cotterill_le_11 : ∀ d, 1 ≤ d → d ≤ 11 → ClemensAtDegree d
  ballico_fontanari_12 : SmoothClemensAtDegree 12

theorem clemens_iff_tail_ge_12 (Q : QuinticThreefoldClemensData) :
    (∀ d, 1 ≤ d → Q.ClemensAtDegree d) ↔ (∀ d, 12 ≤ d → Q.ClemensAtDegree d) := by
  constructor
  · intro hall d hd
    exact hall d (by omega)
  · intro htail d hd1
    by_cases h11 : d ≤ 11
    · exact Q.cotterill_le_11 d hd1 h11
    · exact htail d (by omega)

end ClemensConjecture
