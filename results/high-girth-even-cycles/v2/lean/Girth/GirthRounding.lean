import Girth.IntervalEstimates

namespace GirthVerification

noncomputable def girthLower (n : ℕ) : ℕ := Nat.ceil (40 * Real.log (Real.log (n : ℝ)))
noncomputable def vanishingTime (n : ℕ) : ℕ := 2 * ((girthLower n - 1) / 2)
noncomputable def localMassBound (n : ℕ) : ℝ := 16384 * (8 / 9 : ℝ) ^ vanishingTime n

theorem girthLower_log_le (n : ℕ) :
    40 * Real.log (Real.log (n : ℝ)) ≤ (girthLower n : ℝ) := Nat.le_ceil _

theorem vanishingTime_even (n : ℕ) : Even (vanishingTime n) := even_two_mul _

theorem vanishingTime_bounds (n : ℕ) (hg : 3 ≤ girthLower n) :
    1 ≤ vanishingTime n ∧ vanishingTime n < girthLower n ∧ girthLower n ≤ vanishingTime n + 2 := by
  unfold vanishingTime
  omega

theorem vanishingTime_log_lower (n : ℕ) (hg : 3 ≤ girthLower n) :
    40 * Real.log (Real.log (n : ℝ)) - 2 ≤ (vanishingTime n : ℝ) := by
  have h := (vanishingTime_bounds n hg).2.2
  have hr : (girthLower n : ℝ) ≤ (vanishingTime n : ℝ) + 2 := by exact_mod_cast h
  have hh := girthLower_log_le n
  linarith

theorem localMassBound_nonneg (n : ℕ) : 0 ≤ localMassBound n := by unfold localMassBound; positivity

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem girthLower_le_girth (hgir : HighGirth G) : girthLower (Fintype.card V) ≤ G.girth :=
  Nat.ceil_le.mpr hgir

theorem highCutoff_local_mass_bound (hdeg : MinimumDegreeThree G) (hgir : HighGirth G)
    (hg : 3 ≤ girthLower (Fintype.card V)) (v : V) :
    ∑ i : SlowModes G highCutoff,
      vertexModeWeight G hdeg highCutoff highCutoff_positive highCutoff_outer v i ≤
        localMassBound (Fintype.card V) := by
  have hb := vanishingTime_bounds (Fintype.card V) hg
  have hh := higherCutoff_vertex_mass_le G hdeg lowCutoff lowContour highCutoff
    lowCutoff_positive lowCutoff_outer highCutoff_positive highCutoff_outer lowCutoff_lt_contour
    lowContour_lt_one lowCutoff_lt_highCutoff (vanishingTime (Fintype.card V)) hb.1
    (vanishingTime_even _) (hb.2.1.trans_le (girthLower_le_girth G hgir)) v
  have heq : lowContour / highCutoff = 8 / 9 := by norm_num [lowContour, highCutoff]
  rw [heq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right low_returnConstant_le (by positivity))

end GirthVerification
