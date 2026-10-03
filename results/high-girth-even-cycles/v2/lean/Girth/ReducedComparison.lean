import Girth.ReducedResolvent
import Girth.SlowResolventFormula

namespace GirthVerification

open scoped BigOperators
open WithLp

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem slowProjectorCLM_apply_sum (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (x : EuclideanSpace ℂ G.Dart) :
    slowProjectorCLM G hdeg c hc hcouter x =
      ∑ i : SlowModes G c, slowCoordinate G hdeg c hc hcouter i (ofLp x) •
        toLp 2 (slowVector G hdeg c hc hcouter i) := by
  ext e
  simp [slowProjectorCLM, euclideanEndLift_apply, slowProjector_apply]

theorem resolventMap_slowVector (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) (i : SlowModes G c) :
    resolventMap G w (toLp 2 (slowVector G hdeg c hc hcouter i)) =
      (w - (slowValue G c i : ℂ)) • toLp 2 (slowVector G hdeg c hc hcouter i) := by
  rw [resolventMap_apply, sub_smul]
  congr 1
  ext e
  exact congrFun (slowVector_eigen G hdeg c hc hcouter i) e

theorem resolventMap_comp_fullSlowResolvent (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) (hw : w.im ≠ 0) :
    (resolventMap G w).comp (fullSlowResolvent G hdeg c hc hcouter w) =
      slowProjectorCLM G hdeg c hc hcouter := by
  apply ContinuousLinearMap.ext
  intro x
  change resolventMap G w (fullSlowResolvent G hdeg c hc hcouter w x) = _
  rw [fullSlowResolvent_formula, map_sum, slowProjectorCLM_apply_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, resolventMap_slowVector, smul_smul]
  have hne : w - (slowValue G c i : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im (sub_eq_zero.mp h)
    simp only [Complex.ofReal_im] at him
    exact hw him
  congr 1
  field_simp

/-- Off the real axis the analytic reduced resolvent is exactly the full
inverse minus the constructed slow spectral sum. -/
theorem exists_full_inverse_reduced_comparison (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) (hw : w.im ≠ 0) (hwc : c < ‖w‖) :
    ∃ R : EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart,
      reducedResolvent G hdeg c hc hcouter w = R - fullSlowResolvent G hdeg c hc hcouter w ∧
      ‖R‖ ≤ (2 * ‖w‖ + 1 / 2 + ‖w‖ / (2 * |w.im|)) / (‖w‖ ^ 2 - 1 / 2) := by
  have hr : 1 / 2 < ‖w‖ ^ 2 :=
    hcouter.trans ((sq_lt_sq₀ hc.le (norm_nonneg w)).mpr hwc)
  obtain ⟨R, hR, _, hNorm⟩ := exists_resolvent_with_norm_bound G hdeg w hw hr
  have hInjective := LinearMap.ker_eq_bot.mp (resolventMap_ker_eq_bot G hdeg w hw hr)
  have hsum : reducedResolvent G hdeg c hc hcouter w + fullSlowResolvent G hdeg c hc hcouter w = R := by
    apply ContinuousLinearMap.ext
    intro x
    apply hInjective
    change resolventMap G w (reducedResolvent G hdeg c hc hcouter w x +
      fullSlowResolvent G hdeg c hc hcouter w x) = resolventMap G w (R x)
    rw [map_add]
    have hRed := congrArg (fun T : EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart => T x)
      (resolventMap_comp_reducedResolvent G hdeg c hc hcouter w hwc)
    have hSlow := congrArg (fun T : EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart => T x)
      (resolventMap_comp_fullSlowResolvent G hdeg c hc hcouter w hw)
    have hRx := congrArg (fun T : EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart => T x) hR
    change resolventMap G w (reducedResolvent G hdeg c hc hcouter w x) =
      residualProjectorCLM G hdeg c hc hcouter x at hRed
    change resolventMap G w (fullSlowResolvent G hdeg c hc hcouter w x) =
      slowProjectorCLM G hdeg c hc hcouter x at hSlow
    change resolventMap G w (R x) = x at hRx
    rw [hRed, hSlow, hRx, residualProjectorCLM_eq_sub]
    simp
  refine ⟨R, ?_, hNorm⟩
  exact eq_sub_iff_add_eq.mpr hsum

theorem reducedResolvent_nonreal_norm_bound (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) (hw : w.im ≠ 0) (hwc : c < ‖w‖) :
    ‖reducedResolvent G hdeg c hc hcouter w‖ ≤
      (2 * ‖w‖ + 1 / 2 + ‖w‖ / (2 * |w.im|)) / (‖w‖ ^ 2 - 1 / 2) +
        2 * (c / (2 * c ^ 2 - 1)) / |w.im| := by
  obtain ⟨R, hEq, hNorm⟩ := exists_full_inverse_reduced_comparison G hdeg c hc hcouter w hw hwc
  rw [hEq]
  exact (norm_sub_le _ _).trans (add_le_add hNorm (fullSlowResolvent_norm_le G hdeg c hc hcouter w hw))

end GirthVerification
