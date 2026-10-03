import Girth.RealAxisMeanBound
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace GirthVerification

open scoped InnerProductSpace
open Metric

/-- Scalarization of the exact logarithmic estimate gives a dimension-free
operator bound. No matrix-entry sum, dimension factor, or diagonalizability
hypothesis is used. -/
theorem analytic_operator_norm_bound_from_imaginary {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (R : ℂ → H →L[ℂ] H) (c : ℂ) (η C : ℝ)
    (hη : 0 < η) (hC : 0 < C) (hR : AnalyticOnNhd ℂ R (closedBall c η))
    (hIm : ∀ w ∈ sphere c η, |w.im| ≤ C)
    (hbound : ∀ w ∈ sphere c η, w.im ≠ 0 → ‖R w‖ ≤ C / |w.im|) :
    ‖R c‖ ≤ 2 * C / η := by
  have hscalar : ∀ u v : H, ‖u‖ = 1 → ‖v‖ = 1 → ‖⟪u, R c v⟫_ℂ‖ ≤ 2 * C / η := by
    intro u v hu hv
    let L : (H →L[ℂ] H) →L[ℂ] ℂ := (innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ H v)
    have hf : AnalyticOnNhd ℂ (fun w => ⟪u, R w v⟫_ℂ) (closedBall c η) := by
      intro w hw
      exact (L.analyticAt _).comp (hR w hw)
    apply analytic_norm_bound_from_imaginary (fun w => ⟪u, R w v⟫_ℂ) c η C hη hC hf hIm
    intro w hw him
    calc
      _ ≤ ‖u‖ * ‖R w v‖ := norm_inner_le_norm _ _
      _ = ‖R w v‖ := by rw [hu, one_mul]
      _ ≤ ‖R w‖ * ‖v‖ := (R w).le_opNorm v
      _ = ‖R w‖ := by rw [hv, mul_one]
      _ ≤ _ := hbound w hw him
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity : 0 ≤ 2 * C / η)
  intro v hv
  by_cases hy : R c v = 0
  · simp [hy]
    positivity
  let y := R c v
  have hny : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  let u : H := algebraMap ℝ ℂ ‖y‖⁻¹ • y
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, inv_mul_cancel₀ hny]
  have hself : ‖⟪y, y⟫_ℂ‖ = ‖y‖ ^ 2 := by
    rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq]
  have hinner : ‖⟪u, y⟫_ℂ‖ = ‖y‖ := by
    dsimp only [u]
    rw [inner_smul_left, norm_mul, hself]
    simp [pow_two, hny]
  have h := hscalar u v hu hv
  rwa [hinner] at h

end GirthVerification
