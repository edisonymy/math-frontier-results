import Girth.JensenMean
import Girth.LogImaginaryAverage

namespace GirthVerification

open Metric Real Filter

theorem imaginary_nonzero_codiscrete_sphere (c : ℂ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ w in codiscreteWithin (sphere c |η|), w.im ≠ 0 := by
  let K : ℂ → ℂ := fun w => (imaginaryPartPolynomial c.im η).eval ((w - c) / (η : ℂ))
  have hK : AnalyticOnNhd ℂ K Set.univ := by
    intro w _
    dsimp [K, imaginaryPartPolynomial]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, div_eq_mul_inv]
    fun_prop
  have ha : imaginaryLeading η ≠ 0 := by
    apply norm_pos_iff.mp
    rw [imaginaryLeading_norm η hη]
    positivity
  have hKc : K c ≠ 0 := by simpa [K, imaginaryPartPolynomial] using neg_ne_zero.mpr ha
  have hdisc : ∀ᶠ w in codiscreteWithin (sphere c |η|), K w ≠ 0 :=
    codiscreteWithin.mono (Set.subset_univ _) (hK.preimage_zero_mem_codiscrete hKc)
  filter_upwards [hdisc, self_mem_codiscreteWithin (sphere c |η|)] with w hKw hw
  let z := (w - c) / (η : ℂ)
  have hηc : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have hz : ‖z‖ = 1 := by
    dsimp [z]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    have hn : ‖w - c‖ = |η| := by simpa [mem_sphere, dist_eq_norm] using hw
    rw [hn, div_self (abs_pos.mpr hη.ne').ne']
  have he : c + (η : ℂ) * z = w := by dsimp [z]; field_simp; ring
  have hnorm : ‖K w‖ = |w.im| := by
    rw [show K w = (imaginaryPartPolynomial c.im η).eval z from rfl,
      imaginaryPartPolynomial_norm_unit c.im η z hz]
    have him := congrArg Complex.im he
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] at him
    rw [him]
  intro him
  apply hKw
  apply norm_eq_zero.mp
  rw [hnorm, him, abs_zero]

/-- The apparent `1/|Im|` singularity of an analytic scalar function is
removed by the exact logarithmic mean argument. Real-axis intersections
are discarded only through proved codiscrete circle congruence. -/
theorem analytic_norm_bound_from_imaginary (f : ℂ → ℂ) (c : ℂ) (η C : ℝ)
    (hη : 0 < η) (hC : 0 < C) (hf : AnalyticOnNhd ℂ f (closedBall c η))
    (hIm : ∀ w ∈ sphere c η, |w.im| ≤ C)
    (hbound : ∀ w ∈ sphere c η, w.im ≠ 0 → ‖f w‖ ≤ C / |w.im|) :
    ‖f c‖ ≤ 2 * C / η := by
  by_cases hfc : f c = 0
  · simp [hfc]
    positivity
  let q : ℂ → ℝ := fun w => log C - log |w.im|
  let g : ℂ → ℝ := fun w => if w.im = 0 then log ‖f w‖ else q w
  have hconst : CircleIntegrable (fun _ : ℂ => log C) c η := circleIntegrable_const _ _ _
  have himag := circleIntegrable_log_abs_im c η
  have hq : CircleIntegrable q c η := hconst.sub himag
  have heq : q =ᶠ[codiscreteWithin (sphere c |η|)] g := by
    filter_upwards [imaginary_nonzero_codiscrete_sphere c η hη] with w hw
    simp [g, hw]
  have hg : CircleIntegrable g c η := CircleIntegrable.congr_codiscreteWithin heq hq
  have hf' : AnalyticOnNhd ℂ f (closedBall c |η|) := by simpa [abs_of_pos hη] using hf
  have hlogf : CircleIntegrable (fun w => log ‖f w‖) c η :=
    circleIntegrable_log_norm_meromorphicOn
      ((hf'.mono sphere_subset_closedBall).meromorphicOn)
  have hle : ∀ w ∈ sphere c |η|, log ‖f w‖ ≤ g w := by
    intro w hw
    have hw' : w ∈ sphere c η := by simpa [abs_of_pos hη] using hw
    by_cases him : w.im = 0
    · simp [g, him]
    have hImpos : 0 < |w.im| := abs_pos.mpr him
    have hratio : 0 < C / |w.im| := div_pos hC hImpos
    have hdiv : log (C / |w.im|) = q w := by
      exact log_div hC.ne' hImpos.ne'
    simp only [g, if_neg him]
    rw [← hdiv]
    by_cases hfw : f w = 0
    · rw [hfw, norm_zero, log_zero]
      exact log_nonneg ((one_le_div hImpos).mpr (hIm w hw'))
    · exact log_le_log (norm_pos_iff.mpr hfw) (hbound w hw' him)
  have hm := circleAverage_mono hlogf hg hle
  have havg : circleAverage g c η = log C - circleAverage (fun w : ℂ => log |w.im|) c η := by
    rw [← circleAverage_congr_codiscreteWithin heq hη.ne']
    exact (circleAverage_sub hconst himag).trans (by rw [circleAverage_const])
  have hmean := analytic_log_norm_le_circleAverage f c η hη hf hfc
  have hfloor := log_imaginary_circleAverage_lower c η hη
  have hcenter : log ‖f c‖ ≤ log C - log (η / 2) := by
    rw [havg] at hm
    linarith
  have hlog : log C - log (η / 2) = log (2 * C / η) := by
    rw [log_div (mul_ne_zero two_ne_zero hC.ne') hη.ne', log_mul two_ne_zero hC.ne',
      log_div hη.ne' two_ne_zero]
    ring
  rw [hlog] at hcenter
  exact (log_le_log_iff (norm_pos_iff.mpr hfc) (by positivity : 0 < 2 * C / η)).mp hcenter

end GirthVerification
