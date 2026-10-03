import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Tactic

namespace GirthVerification

open Metric Real

/-- The logarithmic mean-value inequality needed for the real-axis
resolvent estimate, obtained from mathlib's Jensen formula with the
zero contributions checked nonnegative. Boundary zeros are allowed. -/
theorem analytic_log_norm_le_circleAverage (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0) :
    log ‖f c‖ ≤ circleAverage (fun z => log ‖f z‖) c R := by
  have hf' : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR] using hf
  have hc : c ∈ closedBall c |R| := by simp
  have ho : meromorphicOrderAt f c = 0 := by
    rw [(hf' c hc).meromorphicOrderAt_eq, (hf' c hc).analyticOrderAt_eq_zero.mpr hfc]
    rfl
  have hd : MeromorphicOn.divisor f (closedBall c |R|) c = 0 := by
    simp [MeromorphicOn.divisor_apply hf'.meromorphicOn hc, ho]
  have hcoeff := (hf' c hc).meromorphicTrailingCoeffAt_of_ne_zero hfc
  have hJ := hf'.meromorphicOn.circleAverage_log_norm hR.ne'
  have hp : 0 ≤ ∑ᶠ u : ℂ, (MeromorphicOn.divisor f (closedBall c |R|) u : ℝ) *
      log (R * ‖c - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases huc : u = c
    · subst u
      simp [hd]
    by_cases hu : u ∈ closedBall c |R|
    · apply mul_nonneg
      · exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf' u)
      · apply log_nonneg
        have hnorm : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
        apply (le_mul_inv_iff₀ hnorm).mpr
        simpa [mem_closedBall, dist_eq_norm, norm_sub_rev, abs_of_pos hR] using hu
    · simp [(MeromorphicOn.divisor f (closedBall c |R|)).apply_eq_zero_of_notMem hu]
  rw [hd, Int.cast_zero, zero_mul, add_zero, hcoeff] at hJ
  rw [hJ]
  linarith

end GirthVerification
