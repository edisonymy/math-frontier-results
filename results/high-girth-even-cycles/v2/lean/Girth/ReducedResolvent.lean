import Girth.ReducedInverse
import Girth.Resolvent
import Mathlib.Analysis.Normed.Operator.Bilinear

namespace GirthVerification

open WithLp

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def residualInclusion (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    (residualProjector G hdeg c hc hcouter).range →L[ℂ] EuclideanSpace ℂ G.Dart :=
  LinearMap.toContinuousLinearMap (𝕜 := ℂ)
    ((WithLp.linearEquiv 2 ℂ (G.Dart → ℂ)).symm.toLinearMap.comp
      (residualProjector G hdeg c hc hcouter).range.subtype)

theorem residualInclusion_apply (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2)
    (x : (residualProjector G hdeg c hc hcouter).range) :
    residualInclusion G hdeg c hc hcouter x = toLp 2 x.val := rfl

noncomputable def residualRangeMap (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    EuclideanSpace ℂ G.Dart →L[ℂ] (residualProjector G hdeg c hc hcouter).range :=
  LinearMap.toContinuousLinearMap (𝕜 := ℂ)
    (((residualProjector G hdeg c hc hcouter).comp
      (WithLp.linearEquiv 2 ℂ (G.Dart → ℂ)).toLinearMap).codRestrict
        (residualProjector G hdeg c hc hcouter).range (fun x => ⟨ofLp x, rfl⟩))

theorem residualRangeMap_apply (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (x : EuclideanSpace ℂ G.Dart) :
    (residualRangeMap G hdeg c hc hcouter x).val =
      residualProjector G hdeg c hc hcouter (ofLp x) := rfl

theorem residualInclusion_comp_rangeMap (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    (residualInclusion G hdeg c hc hcouter).comp (residualRangeMap G hdeg c hc hcouter) =
      residualProjectorCLM G hdeg c hc hcouter := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem residualInclusion_intertwines (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) :
    (resolventMap G w).comp (residualInclusion G hdeg c hc hcouter) =
      (residualInclusion G hdeg c hc hcouter).comp (reducedResolventMap G hdeg c hc hcouter w) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

noncomputable def reducedResolvent (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) :
    EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart :=
  (residualInclusion G hdeg c hc hcouter).comp
    ((reducedRestrictionInverse G hdeg c hc hcouter w).comp
      (residualRangeMap G hdeg c hc hcouter))

theorem reducedResolvent_analyticOnNhd (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    AnalyticOnNhd ℂ (reducedResolvent G hdeg c hc hcouter) {w : ℂ | c < ‖w‖} := by
  intro w hw
  let E : Type _ := (residualProjector G hdeg c hc hcouter).range
  let H : Type _ := EuclideanSpace ℂ G.Dart
  letI : NormedSpace ℂ E := (inferInstance : NormedSpace ℂ
    (residualProjector G hdeg c hc hcouter).range)
  let L : (E →L[ℂ] E) →L[ℂ] (H →L[ℂ] H) :=
    (ContinuousLinearMap.compL ℂ H E H (residualInclusion G hdeg c hc hcouter)).comp
      ((ContinuousLinearMap.compL ℂ H E E).flip (residualRangeMap G hdeg c hc hcouter))
  have hi := reducedRestrictionInverse_analyticOnNhd G hdeg c hc hcouter w hw
  exact (L.analyticAt _).comp hi

theorem resolventMap_comp_reducedResolvent (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) (hw : c < ‖w‖) :
    (resolventMap G w).comp (reducedResolvent G hdeg c hc hcouter w) =
      residualProjectorCLM G hdeg c hc hcouter := by
  have hA := reducedResolventMap_isUnit G hdeg c hc hcouter w hw
  have hInv : (reducedResolventMap G hdeg c hc hcouter w) *
      reducedRestrictionInverse G hdeg c hc hcouter w = 1 := by
    obtain ⟨a, ha⟩ := hA
    change (reducedResolventMap G hdeg c hc hcouter w) *
      Ring.inverse (reducedResolventMap G hdeg c hc hcouter w) = 1
    rw [← ha, Ring.inverse_unit, Units.mul_inv]
  unfold reducedResolvent
  rw [← ContinuousLinearMap.comp_assoc, residualInclusion_intertwines,
    ContinuousLinearMap.comp_assoc]
  change (residualInclusion G hdeg c hc hcouter).comp
    ((reducedResolventMap G hdeg c hc hcouter w * reducedRestrictionInverse G hdeg c hc hcouter w).comp
      (residualRangeMap G hdeg c hc hcouter)) = _
  rw [hInv]
  exact residualInclusion_comp_rangeMap G hdeg c hc hcouter

end GirthVerification
