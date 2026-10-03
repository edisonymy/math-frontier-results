import Girth.CycleCriterion

namespace GirthVerification

noncomputable def lowCutoff : ℝ := 3 / 4
noncomputable def lowContour : ℝ := 4 / 5
noncomputable def highCutoff : ℝ := 9 / 10
noncomputable def highContour : ℝ := 19 / 20

theorem lowCutoff_positive : 0 < lowCutoff := by norm_num [lowCutoff]
theorem lowCutoff_outer : 1 / 2 < lowCutoff ^ 2 := by norm_num [lowCutoff]
theorem highCutoff_positive : 0 < highCutoff := by norm_num [highCutoff]
theorem highCutoff_outer : 1 / 2 < highCutoff ^ 2 := by norm_num [highCutoff]
theorem lowCutoff_lt_contour : lowCutoff < lowContour := by norm_num [lowCutoff, lowContour]
theorem lowContour_lt_one : lowContour < 1 := by norm_num [lowContour]
theorem lowCutoff_lt_highCutoff : lowCutoff < highCutoff := by norm_num [lowCutoff, highCutoff]
theorem highCutoff_lt_contour : highCutoff < highContour := by norm_num [highCutoff, highContour]
theorem highContour_lt_one : highContour < 1 := by norm_num [highContour]

theorem low_returnConstant_le : returnConstant lowCutoff lowContour ≤ 16384 := by
  norm_num [returnConstant, remainderConstant, cutoffMidpoint, cutoffRadius, lowCutoff, lowContour]

theorem high_returnConstant_le : returnConstant highCutoff highContour ≤ 8192 := by
  norm_num [returnConstant, remainderConstant, cutoffMidpoint, cutoffRadius, highCutoff, highContour]

theorem high_vertexWeightConstant_le : vertexWeightConstant highCutoff ≤ 3 := by
  norm_num [vertexWeightConstant, highCutoff]

theorem high_powerConstant_le :
    2 * highContour * remainderConstant highCutoff highContour / cutoffRadius highCutoff highContour ≤ 8192 := by
  norm_num [remainderConstant, cutoffMidpoint, cutoffRadius, highCutoff, highContour]

theorem log_highContour : Real.log highContour = -Real.log (20 / 19 : ℝ) := by
  have he : highContour = (20 / 19 : ℝ)⁻¹ := by norm_num [highContour]
  rw [he, Real.log_inv]

theorem log_ratio_ge_twentieth : 1 / 20 ≤ Real.log (20 / 19 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num [highContour] : 0 < highContour)
  rw [log_highContour] at h
  norm_num [highContour] at h
  linarith

theorem highContour_three_fourths_le : highContour ^ (3 / 4 : ℝ) ≤ 97 / 100 := by
  have hpow : (highContour ^ (3 / 4 : ℝ)) ^ (4 : ℕ) = highContour ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by norm_num [highContour] : 0 ≤ highContour)]
    rw [show (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num [highContour]) _) (by norm_num) (by decide : (4 : ℕ) ≠ 0)).mp
  rw [hpow]
  norm_num [highContour]

end GirthVerification
