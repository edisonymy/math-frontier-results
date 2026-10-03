import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Algebra.Spectrum

namespace GirthVerification

open Complex Metric

theorem cauchy_coefficient_norm_bound {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (f : ℂ → H) (r K : ℝ) (hr : 0 < r)
    (hbound : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ K) (n : ℕ) :
    ‖cauchyPowerSeries f 0 r n‖ ≤ K * r⁻¹ ^ n := by
  have hInt : (∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap 0 r θ)‖) ≤
      (2 * Real.pi) * K := by
    calc
      _ ≤ ‖∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap 0 r θ)‖‖ := le_abs_self _
      _ ≤ |2 * Real.pi - 0| * K := by
        simpa [mul_comm] using
          intervalIntegral.norm_integral_le_of_norm_le_const
            (a := 0) (b := 2 * Real.pi) (f := fun θ => ‖f (circleMap 0 r θ)‖)
            (fun θ _ => by
              simpa using hbound (circleMap 0 r θ) (circleMap_mem_sphere 0 hr.le θ))
      _ = _ := by simp [Real.pi_pos.le]
  have hAvg : (2 * Real.pi)⁻¹ *
      (∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap 0 r θ)‖) ≤ K := by
    calc
      _ ≤ (2 * Real.pi)⁻¹ * ((2 * Real.pi) * K) :=
        mul_le_mul_of_nonneg_left hInt (by positivity)
      _ = K := by rw [inv_mul_cancel_left₀ (by positivity)]
  exact (norm_cauchyPowerSeries_le f 0 r n).trans (by
    rw [abs_of_pos hr]
    exact mul_le_mul_of_nonneg_right hAvg (by positivity))

/-- Cauchy bounds the actual algebra powers, even for a nonnormal operator.
The differentiability and boundary bound are explicit obligations. -/
theorem inverse_one_sub_power_bound {A H : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (T : A) (L : A →L[ℂ] H) (r K : ℝ) (hr : 0 < r)
    (hd : DifferentiableOn ℂ (fun z : ℂ => L (Ring.inverse (1 - z • T)))
      (closedBall 0 r))
    (hbound : ∀ z ∈ sphere (0 : ℂ) r, ‖L (Ring.inverse (1 - z • T))‖ ≤ K)
    (n : ℕ) : ‖L (T ^ n)‖ ≤ K * r⁻¹ ^ n := by
  let p : FormalMultilinearSeries ℂ ℂ A := fun k =>
    ContinuousMultilinearMap.mkPiRing ℂ (Fin k) (T ^ k)
  have hp := spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ T
  have hLp : HasFPowerSeriesAt (fun z : ℂ => L (Ring.inverse (1 - z • T)))
      (L.compFormalMultilinearSeries p) 0 :=
    (L.comp_hasFPowerSeriesOnBall hp).hasFPowerSeriesAt
  have hc := hd.hasFPowerSeriesOnBall (R := ⟨r, hr.le⟩) hr
  have heq := hLp.eq_formalMultilinearSeries hc.hasFPowerSeriesAt
  have hcoeff : L (T ^ n) = cauchyPowerSeries
      (fun z : ℂ => L (Ring.inverse (1 - z • T))) 0 r n (fun _ => 1) := by
    have he := congrArg (fun s : FormalMultilinearSeries ℂ ℂ H => s n (fun _ => 1)) heq
    simpa [p, ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousMultilinearMap.mkPiRing_apply] using he
  rw [hcoeff]
  calc
    _ ≤ ‖cauchyPowerSeries (fun z : ℂ => L (Ring.inverse (1 - z • T))) 0 r n‖ := by
      simpa using (cauchyPowerSeries (fun z : ℂ => L (Ring.inverse (1 - z • T))) 0 r n).le_opNorm
        (fun _ => 1)
    _ ≤ _ := cauchy_coefficient_norm_bound _ r K hr hbound n

end GirthVerification
