import Girth.NumericalError

namespace GirthVerification

theorem pow_mul_rpow_eq (x : ℝ) (hx : 0 < x) (k : ℕ) (r : ℝ) :
    x ^ k * x ^ r = x ^ ((k : ℝ) + r) := by
  rw [Real.rpow_add hx, Real.rpow_natCast]

/-- A single graph-independent upper bound for all four errors on the
literal theorem interval. -/
theorem numericalError_le_universalError (n N L : ℕ) (hn : 0 < n) (hnN : n ≤ N)
    (hNsq : N ≤ n ^ 2) (hL : 0 < L) (hlog : 0 < Real.log (n : ℝ))
    (hg : 3 ≤ girthLower n)
    (hlower : 4 * Real.log (N : ℝ) / Real.log (20 / 19 : ℝ) ≤ (L : ℝ))
    (hupper : (L : ℝ) ≤ 8 * Real.log (N : ℝ) / Real.log (20 / 19 : ℝ)) :
    numericalError n N L ≤ universalError (n : ℝ) := by
  have hN := hn.trans_le hnN
  have hlen := interval_length_le_log n N L (by omega) hN hNsq hupper
  have hlenSq : (L : ℝ) ^ 2 ≤ (320 * Real.log (n : ℝ)) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg L) (by positivity)).mpr hlen
  have hC := high_vertexWeightConstant_le
  have hC0 := high_vertexWeightConstant_nonneg
  have hE := high_returnConstant_le
  have hE0 := high_returnConstant_nonneg
  have hE2 : returnConstant highCutoff highContour ^ 2 ≤ (8192 : ℝ) ^ 2 :=
    (sq_le_sq₀ hE0 (by norm_num)).mpr hE
  have hmass : localMassBound n ≤
      16384 * (Real.exp (2 / 9) * Real.log (n : ℝ) ^ (-40 / 9 : ℝ)) :=
    mul_le_mul_of_nonneg_left (vanishingTime_geometric_decay n hlog hg) (by norm_num)
  have h1 : vertexWeightConstant highCutoff * (L : ℝ) ^ 2 * localMassBound n ≤
      (3 * 16384 * 320 ^ 2 * Real.exp (2 / 9)) * Real.log (n : ℝ) ^ (-22 / 9 : ℝ) := by
    calc
      _ ≤ 3 * (320 * Real.log (n : ℝ)) ^ 2 *
          (16384 * (Real.exp (2 / 9) * Real.log (n : ℝ) ^ (-40 / 9 : ℝ))) :=
        mul_le_mul (mul_le_mul hC hlenSq (sq_nonneg _) (by norm_num)) hmass
          (localMassBound_nonneg n) (by positivity)
      _ = (3 * 16384 * 320 ^ 2 * Real.exp (2 / 9)) *
          (Real.log (n : ℝ) ^ (2 : ℕ) * Real.log (n : ℝ) ^ (-40 / 9 : ℝ)) := by ring
      _ = _ := by rw [pow_mul_rpow_eq _ hlog]; norm_num
  have hκ := numericalDecay_le N L hN hL hlower
  have hκ0 := numericalDecay_nonneg N L
  have hκg : numericalDecay N L ^ girthLower n ≤ Real.log (n : ℝ) ^ (-6 / 5 : ℝ) :=
    (pow_le_pow_left₀ hκ0 hκ _).trans (girthLower_geometric_decay n hlog)
  have hden := numericalDecay_reciprocal_bound N L hκ
  have hdenpos : 0 < 1 - numericalDecay N L := by linarith
  have h2 : 2 * vertexWeightConstant highCutoff * returnConstant highCutoff highContour * (L : ℝ) *
      numericalDecay N L ^ girthLower n / (1 - numericalDecay N L) ≤
      (2 * 3 * 8192 * 320 * (100 / 3)) * Real.log (n : ℝ) ^ (-1 / 5 : ℝ) := by
    have hprod : 2 * vertexWeightConstant highCutoff * returnConstant highCutoff highContour * (L : ℝ) *
        numericalDecay N L ^ girthLower n ≤
        2 * 3 * 8192 * (320 * Real.log (n : ℝ)) * Real.log (n : ℝ) ^ (-6 / 5 : ℝ) := by
      gcongr <;> first | assumption | positivity
    calc
      _ = (2 * vertexWeightConstant highCutoff * returnConstant highCutoff highContour * (L : ℝ) *
          numericalDecay N L ^ girthLower n) * (1 / (1 - numericalDecay N L)) := by ring
      _ ≤ (2 * 3 * 8192 * (320 * Real.log (n : ℝ)) * Real.log (n : ℝ) ^ (-6 / 5 : ℝ)) * (100 / 3) :=
        mul_le_mul hprod hden (by positivity) (by positivity)
      _ = (2 * 3 * 8192 * 320 * (100 / 3)) *
          (Real.log (n : ℝ) ^ (1 : ℕ) * Real.log (n : ℝ) ^ (-6 / 5 : ℝ)) := by ring
      _ = _ := by rw [pow_mul_rpow_eq _ hlog]; norm_num
  have hρ := interval_geometric_pow_le N L hN hlower
  have hvol := volume_decay_bounds n N hn hnN
  have hv1 : (n : ℝ) * highContour ^ L ≤ (n : ℝ) ^ (-3 : ℝ) :=
    (mul_le_mul_of_nonneg_left hρ (Nat.cast_nonneg n)).trans hvol.1
  have hv2 : (N : ℝ) * highContour ^ L ≤ (n : ℝ) ^ (-3 : ℝ) :=
    (mul_le_mul_of_nonneg_left hρ (Nat.cast_nonneg N)).trans hvol.2
  have h3 : (n : ℝ) * returnConstant highCutoff highContour ^ 2 * (L : ℝ) ^ 2 * highContour ^ L ≤
      (8192 ^ 2 * 320 ^ 2) * Real.log (n : ℝ) ^ (2 : ℕ) * (n : ℝ) ^ (-3 : ℝ) := by
    calc
      _ = (returnConstant highCutoff highContour ^ 2 * (L : ℝ) ^ 2) * ((n : ℝ) * highContour ^ L) := by ring
      _ ≤ ((8192 : ℝ) ^ 2 * (320 * Real.log (n : ℝ)) ^ 2) * (n : ℝ) ^ (-3 : ℝ) :=
        mul_le_mul (mul_le_mul hE2 hlenSq (sq_nonneg _) (by positivity)) hv1 (by
          unfold highContour; positivity) (by positivity)
      _ = _ := by ring
  have h4 : (N : ℝ) * highPowerConstant * highContour ^ L ≤ 8192 * (n : ℝ) ^ (-3 : ℝ) := by
    calc
      _ = highPowerConstant * ((N : ℝ) * highContour ^ L) := by ring
      _ ≤ _ := mul_le_mul high_powerConstant_le hv2 (by unfold highContour; positivity) (by norm_num)
  exact add_le_add (add_le_add (add_le_add h1 h2) h3) h4

end GirthVerification
