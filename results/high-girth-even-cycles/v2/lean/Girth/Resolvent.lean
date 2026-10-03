import Girth.ResidualEstimate
import Mathlib.Analysis.Normed.Operator.Banach

namespace GirthVerification

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def resolventMap (w : ℂ) :
    EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart :=
  w • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ G.Dart) - transitionCLM G

theorem resolventMap_apply (w : ℂ) (x : EuclideanSpace ℂ G.Dart) :
    resolventMap G w x = w • x - transitionCLM G x := rfl

theorem resolventMap_ker_eq_bot (hdeg : MinimumDegreeThree G) (w : ℂ)
    (hw : w.im ≠ 0) (hr : 1 / 2 < ‖w‖ ^ 2) : (resolventMap G w).ker = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have h := residual_lower_bound G hdeg w hw x
  have he : transitionCLM G x - w • x = 0 := by
    change w • x - transitionCLM G x = 0 at hx
    exact sub_eq_zero.mpr (sub_eq_zero.mp hx).symm
  rw [he, norm_zero, mul_zero] at h
  have ha : 0 < ‖w‖ ^ 2 - 1 / 2 := by linarith
  have hn : ‖x‖ ≤ 0 := (mul_le_mul_iff_of_pos_left ha).mp (by simpa using h)
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg x))

/-- An actual two-sided inverse exists at every nonreal point outside the
inner spectral disc, and satisfies precisely the manuscript's display (10).
This includes arbitrary disconnected, irregular graph operators. -/
theorem exists_resolvent_with_norm_bound (hdeg : MinimumDegreeThree G) (w : ℂ)
    (hw : w.im ≠ 0) (hr : 1 / 2 < ‖w‖ ^ 2) :
    ∃ R : EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart,
      (resolventMap G w).comp R = ContinuousLinearMap.id ℂ _ ∧
      R.comp (resolventMap G w) = ContinuousLinearMap.id ℂ _ ∧
      ‖R‖ ≤ (2 * ‖w‖ + 1 / 2 + ‖w‖ / (2 * |w.im|)) / (‖w‖ ^ 2 - 1 / 2) := by
  let A := resolventMap G w
  have hker : A.ker = ⊥ := resolventMap_ker_eq_bot G hdeg w hw hr
  have hsurj : A.range = ⊤ := LinearMap.range_eq_top.mpr
    (LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker))
  let e := ContinuousLinearEquiv.ofBijective A hker hsurj
  let R := e.symm.toContinuousLinearMap
  have hright : ∀ x, A (R x) = x :=
    ContinuousLinearEquiv.ofBijective_apply_symm_apply A hker hsurj
  have hleft : ∀ x, R (A x) = x :=
    ContinuousLinearEquiv.ofBijective_symm_apply_apply A hker hsurj
  refine ⟨R, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    exact hright x
  · apply ContinuousLinearMap.ext
    intro x
    exact hleft x
  · have ha : 0 < ‖w‖ ^ 2 - 1 / 2 := by linarith
    apply ContinuousLinearMap.opNorm_le_bound R (by positivity)
    intro x
    have h := residual_lower_bound G hdeg w hw (R x)
    have he : transitionCLM G (R x) - w • R x = -x := by
      have h := hright x
      change w • R x - transitionCLM G (R x) = x at h
      rw [← neg_sub, h]
    rw [he, norm_neg] at h
    have h' : ‖R x‖ ≤
        ((2 * ‖w‖ + 1 / 2 + ‖w‖ / (2 * |w.im|)) * ‖x‖) / (‖w‖ ^ 2 - 1 / 2) := by
      apply (le_div_iff₀ ha).mpr
      simpa [mul_comm] using h
    convert h' using 1; ring

end GirthVerification
