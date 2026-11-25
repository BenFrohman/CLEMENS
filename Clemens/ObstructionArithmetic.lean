/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Numerical obstruction arithmetic for the Clemens frontier

Records the Riemann–Roch identity for rank-2 bundles on ℙ¹ with degree -2
and the expected dimension of the locus of (1, d-1)-curves on quadrics.
These are combinatorial facts. They do not prove vanishing of H¹(N_f)
for any degree ≥ 12.
-/

namespace ClemensObstruction

def h0Line (n : ℤ) : ℤ := max 0 (n + 1)
def h1Line (n : ℤ) : ℤ := max 0 (-n - 1)

theorem line_riemann_roch (n : ℤ) : h0Line n - h1Line n = n + 1 := by
  unfold h0Line h1Line
  by_cases h : 0 ≤ n + 1
  · have h1 : max 0 (n + 1) = n + 1 := max_eq_right h
    have h2 : max 0 (-n - 1) = 0 := max_eq_left (by linarith)
    linarith
  · have h1 : max 0 (n + 1) = 0 := max_eq_left (by linarith)
    have h2 : max 0 (-n - 1) = -n - 1 := max_eq_right (by linarith)
    linarith

structure Rank2BundleP1 where
  a : ℤ
  b : ℤ

def Rank2BundleP1.deg (E : Rank2BundleP1) : ℤ := E.a + E.b
def Rank2BundleP1.h0 (E : Rank2BundleP1) : ℤ := h0Line E.a + h0Line E.b
def Rank2BundleP1.h1 (E : Rank2BundleP1) : ℤ := h1Line E.a + h1Line E.b
def Rank2BundleP1.chi (E : Rank2BundleP1) : ℤ := E.h0 - E.h1

theorem Rank2BundleP1.riemann_roch (E : Rank2BundleP1) :
    E.chi = E.deg + 2 := by
  unfold Rank2BundleP1.chi Rank2BundleP1.h0 Rank2BundleP1.h1 Rank2BundleP1.deg
  have ha := line_riemann_roch E.a
  have hb := line_riemann_roch E.b
  linarith

theorem normal_bundle_h0_eq_h1 (N : Rank2BundleP1) (hdeg : N.deg = -2) :
    N.chi = 0 ∧ N.h0 = N.h1 := by
  have hrr := N.riemann_roch
  unfold Rank2BundleP1.chi at hrr
  refine ⟨by linarith, by linarith⟩

theorem normal_bundle_unobstructed_iff_balanced (N : Rank2BundleP1) (hdeg : N.deg = -2) :
    N.h1 = 0 ↔ N.a = -1 ∧ N.b = -1 := by
  unfold Rank2BundleP1.deg at hdeg
  unfold Rank2BundleP1.h1 h1Line
  constructor
  · intro hh1
    have ha0 : 0 ≤ max 0 (-N.a - 1) := le_max_left 0 _
    have hb0 : 0 ≤ max 0 (-N.b - 1) := le_max_left 0 _
    have hma : max 0 (-N.a - 1) = 0 := by linarith
    have hmb : max 0 (-N.b - 1) = 0 := by linarith
    have ha_le : -N.a - 1 ≤ 0 := le_of_max_eq_left hma
    have hb_le : -N.b - 1 ≤ 0 := le_of_max_eq_left hmb
    constructor <;> linarith
  · rintro ⟨ha, hb⟩
    rw [ha, hb]
    norm_num

theorem normal_bundle_obstructed_of_unbalanced (N : Rank2BundleP1) (hdeg : N.deg = -2)
    (hunbal : 0 ≤ N.a ∨ 0 ≤ N.b) :
    1 ≤ N.h0 ∧ 1 ≤ N.h1 := by
  have h1_ne : N.h1 ≠ 0 := by
    rw [normal_bundle_unobstructed_iff_balanced N hdeg]
    rintro ⟨ha, hb⟩
    rcases hunbal with ha0 | hb0 <;> linarith
  have h1_nonneg : 0 ≤ N.h1 := by
    unfold Rank2BundleP1.h1 h1Line
    linarith [le_max_left (0 : ℤ) (-N.a - 1), le_max_left (0 : ℤ) (-N.b - 1)]
  have heq : N.h0 = N.h1 := (normal_bundle_h0_eq_h1 N hdeg).2
  constructor <;> linarith

def quadricCurveDegree (d : ℕ) : ℕ := 1 + (d - 1)
def quadricCurveGenus (d : ℕ) : ℕ := (1 - 1) * ((d - 1) - 1)
def quadricLocusDim (d : ℕ) : ℕ := 4 + 9 + (2 * d - 1)
def quinticIncidenceConditions (d : ℕ) : ℕ := 5 * d + 1
def quadricExpectedCodim (d : ℕ) : ℕ :=
  quinticIncidenceConditions d - quadricLocusDim d
def degNormalInQuadric (d : ℕ) : ℕ := 2 * d - 2
def degAmbientQuinticNormal (d : ℕ) : ℕ := 5 * d

theorem quadric_parameter_formulas (d : ℕ) (hd : 4 ≤ d) :
    quadricCurveDegree d = d ∧
    quadricCurveGenus d = 0 ∧
    quadricLocusDim d = 2 * d + 12 ∧
    quadricExpectedCodim d = 3 * d - 11 := by
  unfold quadricCurveDegree quadricCurveGenus quadricLocusDim
    quinticIncidenceConditions quadricExpectedCodim
  omega

theorem d12_quadric_obstruction_numbers :
    quadricLocusDim 12 = 36 ∧
    quinticIncidenceConditions 12 = 61 ∧
    quadricExpectedCodim 12 = 25 ∧
    degNormalInQuadric 12 = 22 ∧
    degAmbientQuinticNormal 12 = 60 := by
  decide

end ClemensObstruction
