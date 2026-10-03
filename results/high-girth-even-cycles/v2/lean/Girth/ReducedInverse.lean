import Girth.EuclideanLift
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Operator.Banach

namespace GirthVerification

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def residualRestrictedCLM (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    (residualProjector G hdeg c hc hcouter).range →L[ℂ]
      (residualProjector G hdeg c hc hcouter).range :=
  LinearMap.toContinuousLinearMap (𝕜 := ℂ) (residualRestrictedEnd G hdeg c hc hcouter)

noncomputable def reducedResolventMap (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) :
    (residualProjector G hdeg c hc hcouter).range →L[ℂ]
      (residualProjector G hdeg c hc hcouter).range :=
  w • ContinuousLinearMap.id ℂ _ - residualRestrictedCLM G hdeg c hc hcouter

theorem reducedResolventMap_ker_eq_bot (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) (hw : c < ‖w‖) :
    (reducedResolventMap G hdeg c hc hcouter w).ker = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  by_contra hxne
  have hPx : residualRestrictedEnd G hdeg c hc hcouter x = w • x := by
    change w • x - residualRestrictedEnd G hdeg c hc hcouter x = 0 at hx
    exact (sub_eq_zero.mp hx).symm
  have he : (residualRestrictedEnd G hdeg c hc hcouter).HasEigenvalue w := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := x)
    exact ⟨Module.End.mem_eigenspace_iff.mpr hPx, hxne⟩
  exact (not_le_of_gt hw) (residualRestrictedEnd_eigenvalue_norm_le G hdeg c hc hcouter w he)

theorem reducedResolventMap_isUnit (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) (hw : c < ‖w‖) :
    IsUnit (reducedResolventMap G hdeg c hc hcouter w) := by
  have hker := reducedResolventMap_ker_eq_bot G hdeg c hc hcouter w hw
  have hi := LinearMap.ker_eq_bot.mp hker
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

noncomputable def reducedRestrictionInverse (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) :
    (residualProjector G hdeg c hc hcouter).range →L[ℂ]
      (residualProjector G hdeg c hc hcouter).range :=
  Ring.inverse (reducedResolventMap G hdeg c hc hcouter w)

/-- Analyticity extends across all removed real outer eigenvalues by
inverting on the actual remaining invariant range. No pole cancellation
or diagonalizability is taken as a premise. -/
theorem reducedRestrictionInverse_analyticOnNhd (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    AnalyticOnNhd ℂ (reducedRestrictionInverse G hdeg c hc hcouter) {w : ℂ | c < ‖w‖} := by
  intro w hw
  have hA := reducedResolventMap_isUnit G hdeg c hc hcouter w hw
  have hInv : AnalyticAt ℂ Ring.inverse (reducedResolventMap G hdeg c hc hcouter w) :=
    (analyticOnNhd_inverse (𝕜 := ℂ)
      (A := (residualProjector G hdeg c hc hcouter).range →L[ℂ]
        (residualProjector G hdeg c hc hcouter).range)) _ hA
  have hAffine : AnalyticAt ℂ (reducedResolventMap G hdeg c hc hcouter) w := by
    unfold reducedResolventMap
    have hid : AnalyticAt ℂ (fun z : ℂ => z) w := analyticAt_id
    have hi : AnalyticAt ℂ (fun _ : ℂ => ContinuousLinearMap.id ℂ
        (residualProjector G hdeg c hc hcouter).range) w := analyticAt_const
    have hp : AnalyticAt ℂ (fun _ : ℂ => residualRestrictedCLM G hdeg c hc hcouter) w := analyticAt_const
    exact (hid.smul hi).sub hp
  exact hInv.comp hAffine

end GirthVerification
