import Girth.UniversalErrorBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace GirthVerification

open Filter
open scoped Topology

theorem universalError_tendsto_zero : Tendsto universalError atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ (-22 / 9 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 22 / 9)).comp Real.tendsto_log_atTop
  have h2 : Tendsto (fun x : ℝ => Real.log x ^ (-1 / 5 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp Real.tendsto_log_atTop
  have h3a : Tendsto (fun x : ℝ => Real.log x ^ (2 : ℕ) / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h3b : Tendsto (fun x : ℝ => x ^ (-2 : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)
  have h3 : Tendsto (fun x : ℝ => Real.log x ^ (2 : ℕ) * x ^ (-3 : ℝ)) atTop (𝓝 0) := by
    have heq : (fun x : ℝ => (Real.log x ^ (2 : ℕ) / x) * x ^ (-2 : ℝ)) =ᶠ[atTop]
        (fun x : ℝ => Real.log x ^ (2 : ℕ) * x ^ (-3 : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have h2eq : x ^ (-2 : ℝ) = (x ^ (2 : ℕ))⁻¹ := by
        simpa only [Nat.cast_ofNat] using rpow_negative_nat x hx.le 2
      have h3eq : x ^ (-3 : ℝ) = (x ^ (3 : ℕ))⁻¹ := by
        simpa only [Nat.cast_ofNat] using rpow_negative_nat x hx.le 3
      rw [h2eq, h3eq]
      field_simp
    simpa using (h3a.mul h3b).congr' heq
  have h4 : Tendsto (fun x : ℝ => x ^ (-3 : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)
  have hh := ((h1.const_mul (3 * 16384 * 320 ^ 2 * Real.exp (2 / 9))).add
    (h2.const_mul (2 * 3 * 8192 * 320 * (100 / 3)))).add
      (h3.const_mul (8192 ^ 2 * 320 ^ 2)) |>.add (h4.const_mul 8192)
  convert hh using 1
  · funext x
    unfold universalError
    ring
  · norm_num

/-- The threshold is absolute: the eventual predicates depend only on the
vertex count and fixed numerical constants. -/
theorem exists_universal_threshold : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    0 < n ∧ 0 < Real.log (n : ℝ) ∧ 3 ≤ girthLower n ∧ universalError (n : ℝ) < 1 := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hcast
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have herr : ∀ᶠ n : ℕ in atTop, universalError (n : ℝ) < 1 :=
    (universalError_tendsto_zero.comp hcast).eventually_lt_const (by norm_num)
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog.eventually_gt_atTop 0,
    hloglog.eventually_ge_atTop 1, herr] with n hn hln hll he
  refine ⟨by omega, hln, ?_, he⟩
  dsimp only [Function.comp_def] at hll
  have hg := girthLower_log_le n
  have hgr : (3 : ℝ) ≤ (girthLower n : ℝ) := by linarith
  exact_mod_cast hgr

end GirthVerification
