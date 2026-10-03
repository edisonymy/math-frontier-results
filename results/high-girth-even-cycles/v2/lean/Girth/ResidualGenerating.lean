import Girth.ReducedResolvent
import Girth.CauchyCoefficient

namespace GirthVerification

set_option synthInstance.maxHeartbeats 200000

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def residualSandwich (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    ((residualProjector G hdeg c hc hcouter).range →L[ℂ]
      (residualProjector G hdeg c hc hcouter).range) →L[ℂ]
      (EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart) := by
  let E : Type _ := (residualProjector G hdeg c hc hcouter).range
  letI : NormedSpace ℂ E := (inferInstance : NormedSpace ℂ
    (residualProjector G hdeg c hc hcouter).range)
  exact (ContinuousLinearMap.compL ℂ (EuclideanSpace ℂ G.Dart) E
    (EuclideanSpace ℂ G.Dart) (residualInclusion G hdeg c hc hcouter)).comp
      ((ContinuousLinearMap.compL ℂ (EuclideanSpace ℂ G.Dart) E E).flip
        (residualRangeMap G hdeg c hc hcouter))

noncomputable def residualGenerating (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (z : ℂ) :=
  residualSandwich G hdeg c hc hcouter
    (Ring.inverse (1 - z • residualRestrictedCLM G hdeg c hc hcouter))

theorem residualGeneratingMap_isUnit (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (z : ℂ) (hz : c * ‖z‖ < 1) :
    IsUnit (1 - z • residualRestrictedCLM G hdeg c hc hcouter) := by
  by_cases hz0 : z = 0
  · have hzero : 1 - z • residualRestrictedCLM G hdeg c hc hcouter =
        (1 : (residualProjector G hdeg c hc hcouter).range →L[ℂ]
          (residualProjector G hdeg c hc hcouter).range) := by
      apply ContinuousLinearMap.ext
      intro x
      simp [hz0]
    rw [hzero]
    exact isUnit_one
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hw : c < ‖z⁻¹‖ := by
    rw [norm_inv]
    rw [inv_eq_one_div]
    exact (lt_div_iff₀ hn).mpr (by simpa using hz)
  have hi : Function.Injective (1 - z • residualRestrictedCLM G hdeg c hc hcouter :
      (residualProjector G hdeg c hc hcouter).range →L[ℂ]
        (residualProjector G hdeg c hc hcouter).range) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    by_contra hxne
    have hzTx : z • residualRestrictedCLM G hdeg c hc hcouter x = x := by
      change x - z • residualRestrictedCLM G hdeg c hc hcouter x = 0 at hx
      exact (sub_eq_zero.mp hx).symm
    have hPx : residualRestrictedEnd G hdeg c hc hcouter x = z⁻¹ • x := by
      calc
        _ = z⁻¹ • (z • residualRestrictedCLM G hdeg c hc hcouter x) :=
          (inv_smul_smul₀ hz0 _).symm
        _ = _ := by rw [hzTx]
    have he : (residualRestrictedEnd G hdeg c hc hcouter).HasEigenvalue z⁻¹ := by
      apply Module.End.hasEigenvalue_of_hasEigenvector (x := x)
      exact ⟨Module.End.mem_eigenspace_iff.mpr hPx, hxne⟩
    exact (not_le_of_gt hw)
      (residualRestrictedEnd_eigenvalue_norm_le G hdeg c hc hcouter z⁻¹ he)
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

theorem residualGenerating_analyticAt (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (z : ℂ) (hz : c * ‖z‖ < 1) :
    AnalyticAt ℂ (residualGenerating G hdeg c hc hcouter) z := by
  have hU := residualGeneratingMap_isUnit G hdeg c hc hcouter z hz
  let B : ℂ → ((residualProjector G hdeg c hc hcouter).range →L[ℂ]
      (residualProjector G hdeg c hc hcouter).range) :=
    fun w => 1 - w • residualRestrictedCLM G hdeg c hc hcouter
  have hInv : AnalyticAt ℂ Ring.inverse (B z) :=
    (analyticOnNhd_inverse (𝕜 := ℂ)
    (A := (residualProjector G hdeg c hc hcouter).range →L[ℂ]
      (residualProjector G hdeg c hc hcouter).range)) _ hU
  have hAff : AnalyticAt ℂ B z := by
    have hid : AnalyticAt ℂ (fun w : ℂ => w) z := analyticAt_id
    have ht : AnalyticAt ℂ (fun _ : ℂ => residualRestrictedCLM G hdeg c hc hcouter) z :=
      analyticAt_const
    have hOne : AnalyticAt ℂ (fun _ : ℂ =>
        (1 : (residualProjector G hdeg c hc hcouter).range →L[ℂ]
          (residualProjector G hdeg c hc hcouter).range)) z := analyticAt_const
    exact hOne.sub (hid.smul ht)
  exact ((residualSandwich G hdeg c hc hcouter).analyticAt _).comp (hInv.comp hAff)

theorem residualGenerating_eq_resolvent (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (z : ℂ) (hz0 : z ≠ 0)
    (hz : c * ‖z‖ < 1) :
    residualGenerating G hdeg c hc hcouter z =
      z⁻¹ • reducedResolvent G hdeg c hc hcouter z⁻¹ := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hw : c < ‖z⁻¹‖ := by
    rw [norm_inv, inv_eq_one_div]
    exact (lt_div_iff₀ hn).mpr (by simpa using hz)
  have hA := reducedResolventMap_isUnit G hdeg c hc hcouter z⁻¹ hw
  have hB := residualGeneratingMap_isUnit G hdeg c hc hcouter z hz
  have heq : Ring.inverse (1 - z • residualRestrictedCLM G hdeg c hc hcouter) =
      z⁻¹ • reducedRestrictionInverse G hdeg c hc hcouter z⁻¹ := by
    have hprod : 1 = (1 - z • residualRestrictedCLM G hdeg c hc hcouter) *
        (z⁻¹ • reducedRestrictionInverse G hdeg c hc hcouter z⁻¹) := by
      have hmap : 1 - z • residualRestrictedCLM G hdeg c hc hcouter =
          z • reducedResolventMap G hdeg c hc hcouter z⁻¹ := by
        apply ContinuousLinearMap.ext
        intro x
        simp [reducedResolventMap, smul_sub, smul_smul, hz0]
      rw [hmap]
      have hcancel := Ring.mul_inverse_cancel _ hA
      apply ContinuousLinearMap.ext
      intro x
      have hcx := congrArg (fun T => T x) hcancel
      change x = z • (reducedResolventMap G hdeg c hc hcouter z⁻¹
        (z⁻¹ • reducedRestrictionInverse G hdeg c hc hcouter z⁻¹ x))
      rw [map_smul, smul_smul, mul_inv_cancel₀ hz0, one_smul]
      exact hcx.symm
    simpa only [mul_one] using
      (Ring.inverse_mul_eq_iff_eq_mul _ 1 _ hB).mpr hprod
  unfold residualGenerating reducedResolvent
  rw [heq]
  rw [map_smul]
  rfl

theorem residualInclusion_transition (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    (residualInclusion G hdeg c hc hcouter).comp (residualRestrictedCLM G hdeg c hc hcouter) =
      (transitionCLM G).comp (residualInclusion G hdeg c hc hcouter) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem residualSandwich_pow (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (n : ℕ) :
    residualSandwich G hdeg c hc hcouter (residualRestrictedCLM G hdeg c hc hcouter ^ n) =
      transitionCLM G ^ n * residualProjectorCLM G hdeg c hc hcouter := by
  have hi : ∀ k : ℕ, (residualInclusion G hdeg c hc hcouter).comp
      (residualRestrictedCLM G hdeg c hc hcouter ^ k) =
      (transitionCLM G ^ k).comp (residualInclusion G hdeg c hc hcouter) := by
    intro k
    induction k with
    | zero => simp [ContinuousLinearMap.one_def]
    | succ k ih =>
      rw [pow_succ, pow_succ]
      simp only [ContinuousLinearMap.mul_def]
      rw [← ContinuousLinearMap.comp_assoc, ih, ContinuousLinearMap.comp_assoc,
        residualInclusion_transition, ← ContinuousLinearMap.comp_assoc]
  change (residualInclusion G hdeg c hc hcouter).comp
    ((residualRestrictedCLM G hdeg c hc hcouter ^ n).comp
      (residualRangeMap G hdeg c hc hcouter)) = _
  rw [← ContinuousLinearMap.comp_assoc, hi, ContinuousLinearMap.comp_assoc,
    residualInclusion_comp_rangeMap]
  rfl

end GirthVerification
