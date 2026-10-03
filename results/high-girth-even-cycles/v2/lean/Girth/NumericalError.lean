import Girth.GirthDecay

namespace GirthVerification

noncomputable def numericalDecay (N L : ℕ) : ℝ := highContour * (N : ℝ) ^ (1 / (L : ℝ))
noncomputable def highPowerConstant : ℝ :=
  2 * highContour * remainderConstant highCutoff highContour / cutoffRadius highCutoff highContour

noncomputable def numericalError (n N L : ℕ) : ℝ :=
  vertexWeightConstant highCutoff * (L : ℝ) ^ 2 * localMassBound n +
  2 * vertexWeightConstant highCutoff * returnConstant highCutoff highContour * (L : ℝ) *
    numericalDecay N L ^ girthLower n / (1 - numericalDecay N L) +
  (n : ℝ) * returnConstant highCutoff highContour ^ 2 * (L : ℝ) ^ 2 * highContour ^ L +
  (N : ℝ) * highPowerConstant * highContour ^ L

noncomputable def universalError (x : ℝ) : ℝ :=
  (3 * 16384 * 320 ^ 2 * Real.exp (2 / 9)) * Real.log x ^ (-22 / 9 : ℝ) +
  (2 * 3 * 8192 * 320 * (100 / 3)) * Real.log x ^ (-1 / 5 : ℝ) +
  (8192 ^ 2 * 320 ^ 2) * Real.log x ^ (2 : ℕ) * x ^ (-3 : ℝ) +
  8192 * x ^ (-3 : ℝ)

theorem numericalDecay_nonneg (N L : ℕ) : 0 ≤ numericalDecay N L := by
  unfold numericalDecay highContour
  positivity

theorem numericalDecay_le (N L : ℕ) (hN : 0 < N) (hL : 0 < L)
    (hlower : 4 * Real.log (N : ℝ) / Real.log (20 / 19 : ℝ) ≤ (L : ℝ)) :
    numericalDecay N L ≤ 97 / 100 := interval_collisionDecay_le N L hN hL hlower

theorem numericalDecay_reciprocal_bound (N L : ℕ) (h : numericalDecay N L ≤ 97 / 100) :
    1 / (1 - numericalDecay N L) ≤ 100 / 3 := by
  have hh : 3 / 100 ≤ 1 - numericalDecay N L := by linarith
  have hdiv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 100) hh
  norm_num at hdiv
  simpa only [one_div] using hdiv

theorem high_returnConstant_nonneg : 0 ≤ returnConstant highCutoff highContour := by
  norm_num [returnConstant, remainderConstant, cutoffMidpoint, cutoffRadius, highCutoff, highContour]

theorem high_vertexWeightConstant_nonneg : 0 ≤ vertexWeightConstant highCutoff := by
  norm_num [vertexWeightConstant, highCutoff]

theorem highPowerConstant_nonneg : 0 ≤ highPowerConstant := by
  norm_num [highPowerConstant, remainderConstant, cutoffMidpoint, cutoffRadius, highCutoff, highContour]

theorem rpow_negative_nat (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : x ^ (-(k : ℝ)) = (x ^ k)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_natCast]

theorem volume_decay_bounds (n N : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    (n : ℝ) * (N : ℝ) ^ (-4 : ℝ) ≤ (n : ℝ) ^ (-3 : ℝ) ∧
      (N : ℝ) * (N : ℝ) ^ (-4 : ℝ) ≤ (n : ℝ) ^ (-3 : ℝ) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hNr : (0 : ℝ) < N := by exact_mod_cast (hn.trans_le hnN)
  have hle : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have h4 : (n : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ hnr.le hle 4
  have h3 : (n : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ hnr.le hle 3
  have hninv : (n : ℝ) * ((n : ℝ) ^ 4)⁻¹ = ((n : ℝ) ^ 3)⁻¹ := by field_simp
  have hNinv : (N : ℝ) * ((N : ℝ) ^ 4)⁻¹ = ((N : ℝ) ^ 3)⁻¹ := by field_simp
  have hpow4 : (N : ℝ) ^ (-4 : ℝ) = ((N : ℝ) ^ (4 : ℕ))⁻¹ := by
    simpa only [Nat.cast_ofNat] using rpow_negative_nat (N : ℝ) hNr.le 4
  have hpow3 : (n : ℝ) ^ (-3 : ℝ) = ((n : ℝ) ^ (3 : ℕ))⁻¹ := by
    simpa only [Nat.cast_ofNat] using rpow_negative_nat (n : ℝ) hnr.le 3
  rw [hpow4, hpow3]
  constructor
  · rw [← hninv]
    exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ (pow_pos hNr 4) (pow_pos hnr 4)).mpr h4) hnr.le
  · rw [hNinv]
    exact (inv_le_inv₀ (pow_pos hNr 3) (pow_pos hnr 3)).mpr h3

end GirthVerification
