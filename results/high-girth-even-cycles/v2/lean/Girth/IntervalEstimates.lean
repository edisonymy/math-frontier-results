import Girth.FixedConstants

namespace GirthVerification

theorem interval_length_le_log (n N L : ℕ) (hn : 1 ≤ n) (hN : 0 < N) (hNsq : N ≤ n ^ 2)
    (hupper : (L : ℝ) ≤ 8 * Real.log (N : ℝ) / Real.log (20 / 19 : ℝ)) :
    (L : ℝ) ≤ 320 * Real.log (n : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log (N : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    calc
      _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log hNr (by exact_mod_cast hNsq)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hl := (le_div_iff₀ log_ratio_pos).mp hupper
  have hla := mul_le_mul_of_nonneg_left log_ratio_ge_twentieth (Nat.cast_nonneg L)
  nlinarith

theorem interval_geometric_pow_le (N L : ℕ) (hN : 0 < N)
    (hlower : 4 * Real.log (N : ℝ) / Real.log (20 / 19 : ℝ) ≤ (L : ℝ)) :
    highContour ^ L ≤ (N : ℝ) ^ (-4 : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hl := (div_le_iff₀ log_ratio_pos).mp hlower
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num [highContour] : 0 < highContour),
    Real.rpow_def_of_pos hNr, log_highContour]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem interval_collisionDecay_le (N L : ℕ) (hN : 0 < N) (hL : 0 < L)
    (hlower : 4 * Real.log (N : ℝ) / Real.log (20 / 19 : ℝ) ≤ (L : ℝ)) :
    highContour * (N : ℝ) ^ (1 / (L : ℝ)) ≤ 97 / 100 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hl := (div_le_iff₀ log_ratio_pos).mp hlower
  have hdiv : Real.log (N : ℝ) / L ≤ Real.log (20 / 19 : ℝ) / 4 := by
    apply (div_le_iff₀ hLr).mpr
    nlinarith
  apply le_trans _ highContour_three_fourths_le
  rw [Real.rpow_def_of_pos hNr, Real.rpow_def_of_pos (by norm_num [highContour] : 0 < highContour)]
  nth_rw 1 [← Real.exp_log (by norm_num [highContour] : 0 < highContour)]
  rw [← Real.exp_add, log_highContour]
  apply Real.exp_le_exp.mpr
  ring_nf at hdiv ⊢
  linarith

end GirthVerification
