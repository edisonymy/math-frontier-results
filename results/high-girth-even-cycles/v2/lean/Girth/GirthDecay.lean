import Girth.GirthRounding

namespace GirthVerification

theorem vanishingTime_geometric_decay (n : ℕ) (hlog : 0 < Real.log (n : ℝ))
    (hg : 3 ≤ girthLower n) :
    (8 / 9 : ℝ) ^ vanishingTime n ≤ Real.exp (2 / 9) * (Real.log (n : ℝ)) ^ (-40 / 9 : ℝ) := by
  have hβ := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8 / 9)
  have ht := vanishingTime_log_lower n hg
  have hmul := mul_le_mul_of_nonneg_right hβ (Nat.cast_nonneg (vanishingTime n))
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 8 / 9),
    Real.rpow_def_of_pos hlog, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem girthLower_geometric_decay (n : ℕ) (hlog : 0 < Real.log (n : ℝ)) :
    (97 / 100 : ℝ) ^ girthLower n ≤ (Real.log (n : ℝ)) ^ (-6 / 5 : ℝ) := by
  have hq := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 97 / 100)
  have hg := girthLower_log_le n
  have hmul := mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg (girthLower n))
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 97 / 100),
    Real.rpow_def_of_pos hlog]
  apply Real.exp_le_exp.mpr
  nlinarith

end GirthVerification
