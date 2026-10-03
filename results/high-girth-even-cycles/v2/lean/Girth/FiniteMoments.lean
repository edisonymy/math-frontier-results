import Mathlib.Analysis.MeanInequalities

namespace GirthVerification

theorem weighted_young_nat_powers (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (t s : ℕ) (ht : 0 < t) (hs : 0 < s) :
    x ^ t * y ^ s ≤ (t : ℝ) / (t + s : ℕ) * x ^ (t + s) +
      (s : ℝ) / (t + s : ℕ) * y ^ (t + s) := by
  have hL : (0 : ℝ) < (t + s : ℕ) := by exact_mod_cast (by omega : 0 < t + s)
  have hθ : (t : ℝ) / (t + s : ℕ) + (s : ℝ) / (t + s : ℕ) = 1 := by
    push_cast
    field_simp
  have hxpow : (x ^ (t + s)) ^ ((t : ℝ) / (t + s : ℕ)) = x ^ t := by
    rw [← Real.rpow_natCast x (t + s), ← Real.rpow_mul hx]
    have he : ((t + s : ℕ) : ℝ) * ((t : ℝ) / (t + s : ℕ)) = t := by field_simp
    rw [he, Real.rpow_natCast]
  have hypow : (y ^ (t + s)) ^ ((s : ℝ) / (t + s : ℕ)) = y ^ s := by
    rw [← Real.rpow_natCast y (t + s), ← Real.rpow_mul hy]
    have he : ((t + s : ℕ) : ℝ) * ((s : ℝ) / (t + s : ℕ)) = s := by field_simp
    rw [he, Real.rpow_natCast]
  have h := Real.geom_mean_le_arith_mean2_weighted
    (by positivity : 0 ≤ (t : ℝ) / (t + s : ℕ))
    (by positivity : 0 ≤ (s : ℝ) / (t + s : ℕ))
    (pow_nonneg hx (t + s)) (pow_nonneg hy (t + s)) hθ
  rwa [hxpow, hypow] at h

/-- Finite Hölder with natural moments, retaining the cardinality exponent. -/
theorem finite_lower_moment_bound {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (t s : ℕ) (ht : 0 < t) (hs : 0 < s) :
    ∑ i, a i ^ s ≤ (Fintype.card ι : ℝ) ^ ((t : ℝ) / (t + s : ℕ)) *
      (∑ i, a i ^ (t + s)) ^ ((s : ℝ) / (t + s : ℕ)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hL : (0 : ℝ) < (t + s : ℕ) := by exact_mod_cast (by omega : 0 < t + s)
  let p : ℝ := (t + s : ℕ) / (s : ℝ)
  have hp : 1 ≤ p := by
    apply (le_div_iff₀ hsR).mpr
    dsimp [p]
    norm_cast
    omega
  have hpinv : p⁻¹ = (s : ℝ) / (t + s : ℕ) := by dsimp [p]; rw [inv_div]
  have hθ : 1 - p⁻¹ = (t : ℝ) / (t + s : ℕ) := by
    rw [hpinv]
    push_cast
    field_simp
    ring
  have hpow : ∀ i, (a i ^ s) ^ p = a i ^ (t + s) := by
    intro i
    rw [← Real.rpow_natCast (a i) s, ← Real.rpow_mul (ha i)]
    have he : (s : ℝ) * p = (t + s : ℕ) := by dsimp [p]; field_simp
    rw [he, Real.rpow_natCast]
  have h := Real.inner_le_weight_mul_Lp_of_nonneg Finset.univ hp (fun _ : ι => 1)
    (fun i => a i ^ s) (fun _ => zero_le_one) (fun i => pow_nonneg (ha i) _)
  rw [hθ, hpinv] at h
  simpa only [one_mul, hpow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] using h

end GirthVerification
