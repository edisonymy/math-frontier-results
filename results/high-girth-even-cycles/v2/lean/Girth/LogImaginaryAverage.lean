import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic

namespace GirthVerification

open Polynomial Real Metric

noncomputable def imaginaryLeading (η : ℝ) : ℂ := -Complex.I * ((η / 2 : ℝ) : ℂ)

noncomputable def imaginaryPartPolynomial (y η : ℝ) : ℂ[X] :=
  C (imaginaryLeading η) * X ^ 2 + C (y : ℂ) * X + C (-imaginaryLeading η)

theorem imaginaryPartPolynomial_eval_unit (y η : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    (imaginaryPartPolynomial y η).eval z = z * ((y + η * z.im : ℝ) : ℂ) := by
  have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    simpa [Complex.normSq_apply, pow_two] using h
  have hηsq : η * (z.re ^ 2 + z.im ^ 2) = η := by rw [hsq, mul_one]
  apply Complex.ext
  · simp [imaginaryPartPolynomial, imaginaryLeading, Complex.mul_re, Complex.mul_im, pow_two]
    ring
  · simp [imaginaryPartPolynomial, imaginaryLeading, Complex.mul_re, Complex.mul_im, pow_two]
    nlinarith [hηsq]

theorem imaginaryPartPolynomial_norm_unit (y η : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(imaginaryPartPolynomial y η).eval z‖ = |y + η * z.im| := by
  rw [imaginaryPartPolynomial_eval_unit y η z hz, norm_mul, hz, one_mul, Complex.norm_real]
  exact Real.norm_eq_abs _

theorem imaginaryLeading_norm (η : ℝ) (hη : 0 < η) : ‖imaginaryLeading η‖ = η / 2 := by
  simp [imaginaryLeading, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]

theorem log_imaginary_circle_eq_logMahlerMeasure (c : ℂ) (η : ℝ) :
    circleAverage (fun w : ℂ => log |w.im|) c η =
      (imaginaryPartPolynomial c.im η).logMahlerMeasure := by
  rw [Polynomial.logMahlerMeasure_def, circleAverage, circleAverage]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  have hz : ‖circleMap 0 1 θ‖ = 1 := by simp [norm_circleMap_zero]
  dsimp only
  rw [imaginaryPartPolynomial_norm_unit c.im η _ hz]
  congr 2
  simp [circleMap, Complex.mul_im]

theorem circleIntegrable_log_abs_im (c : ℂ) (η : ℝ) :
    CircleIntegrable (fun w : ℂ => log |w.im|) c η := by
  have hp := (imaginaryPartPolynomial c.im η).intervalIntegrable_mahlerMeasure
  change IntervalIntegrable (fun θ => log |(circleMap c η θ).im|) MeasureTheory.volume 0 (2 * π)
  convert hp using 1
  ext θ
  have hz : ‖circleMap 0 1 θ‖ = 1 := by simp [norm_circleMap_zero]
  rw [imaginaryPartPolynomial_norm_unit c.im η _ hz]
  congr 2
  simp [circleMap, Complex.mul_im]

/-- The exact logarithmic sine-average bound in display (11), including
circles crossing or tangent to the real axis and their integrable zeros. -/
theorem log_imaginary_circleAverage_lower (c : ℂ) (η : ℝ) (hη : 0 < η) :
    log (η / 2) ≤ circleAverage (fun w : ℂ => log |w.im|) c η := by
  rw [log_imaginary_circle_eq_logMahlerMeasure,
    Polynomial.logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots]
  have ha : imaginaryLeading η ≠ 0 := by
    apply norm_pos_iff.mp
    rw [imaginaryLeading_norm η hη]
    positivity
  rw [imaginaryPartPolynomial, Polynomial.leadingCoeff_quadratic ha, imaginaryLeading_norm η hη]
  have hp : 0 ≤ ((imaginaryPartPolynomial c.im η).roots.map (fun z => log⁺ ‖z‖)).sum :=
    Multiset.sum_nonneg (by intro r hr; obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hr; exact posLog_nonneg)
  dsimp only [imaginaryPartPolynomial] at hp
  linarith

end GirthVerification
