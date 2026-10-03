import Girth.EuclideanOperator

namespace GirthVerification

open scoped InnerProductSpace

theorem square_lower_from_triangle (a b e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : b ≤ a + e) : b ^ 2 - 2 * b * e ≤ a ^ 2 := by
  by_cases heb : e ≤ b
  · have hsq := (sq_le_sq₀ (sub_nonneg.mpr heb) ha).mpr (show b - e ≤ a by linarith)
    nlinarith [sq_nonneg e]
  · have hbe : b ≤ e := le_of_not_ge heb
    have hp := mul_nonneg hb (sub_nonneg.mpr hbe)
    nlinarith [sq_nonneg a, sq_nonneg b]

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The lower residual bound underlying display (10), with constants
independent of vertex count, edge count, maximum degree, and connectivity. -/
theorem normalized_residual_lower_bound (hdeg : MinimumDegreeThree G)
    (w : ℂ) (hw : w.im ≠ 0) (x : EuclideanSpace ℂ G.Dart) (hx : ‖x‖ = 1) :
    ‖w‖ ^ 2 - 1 / 2 ≤
      (2 * ‖w‖ + 1 / 2 + ‖w‖ / (2 * |w.im|)) *
        ‖transitionCLM G x - w • x‖ := by
  let y := transitionCLM G x - w • x
  let q := ⟪x, reversalCLM G x⟫_ℂ
  let u := ⟪x, reversalCLM G y⟫_ℂ
  let r := ⟪x, reversalCLM G (transitionCLM G x)⟫_ℂ
  have hqim : q.im = 0 := (reversalCLM_isSymmetric G).im_inner_self_apply x
  have hrim : r.im = 0 := by
    have h := (reversalTransitionCLM_isSymmetric G).im_inner_self_apply x
    simpa [reversalTransitionCLM_eq_comp, ContinuousLinearMap.comp_apply, r] using h
  have hPy : transitionCLM G x = w • x + y := by dsimp [y]; abel
  have hrel : r = w * q + u := by
    dsimp [r, q, u]
    rw [hPy, map_add, map_smul, inner_add_right, inner_smul_right]
  have hu : ‖u‖ ≤ ‖y‖ := by
    simpa [u, hx, reversalCLM_norm] using norm_inner_le_norm x (reversalCLM G y)
  have him : w.im * q.re = -u.im := by
    have h := congrArg Complex.im hrel
    simp only [Complex.add_im, Complex.mul_im, hqim, hrim, mul_zero, zero_add] at h
    linarith
  have hmul : |w.im| * |q.re| ≤ ‖y‖ := by
    rw [← abs_mul, him, abs_neg]
    exact le_trans (Complex.abs_im_le_norm u) hu
  have habs : 0 < |w.im| := abs_pos.mpr hw
  have hq : |q.re| ≤ ‖y‖ / |w.im| := by
    apply (le_div_iff₀ habs).mpr
    simpa [mul_comm] using hmul
  have hure : u.re ≤ ‖y‖ :=
    (le_abs_self u.re).trans ((Complex.abs_re_le_norm u).trans hu)
  have hprod : w.re * q.re ≤ ‖w‖ * |q.re| := by
    calc
      _ ≤ |w.re * q.re| := le_abs_self _
      _ = |w.re| * |q.re| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm w) (abs_nonneg _)
  have hr : r.re ≤ (‖w‖ / |w.im| + 1) * ‖y‖ := by
    have h := congrArg Complex.re hrel
    simp only [Complex.add_re, Complex.mul_re, hqim, mul_zero, sub_zero] at h
    have hp := mul_le_mul_of_nonneg_left hq (norm_nonneg w)
    rw [h]
    calc
      _ ≤ ‖w‖ * (‖y‖ / |w.im|) + ‖y‖ := add_le_add (hprod.trans hp) hure
      _ = _ := by ring
  have htriangle : ‖w‖ ≤ ‖transitionCLM G x‖ + ‖y‖ := by
    calc
      ‖w‖ = ‖w • x‖ := by simp [norm_smul, hx]
      _ = ‖transitionCLM G x - y‖ := by congr 1; dsimp [y]; abel
      _ ≤ _ := norm_sub_le _ _
  have hlower := square_lower_from_triangle ‖transitionCLM G x‖ ‖w‖ ‖y‖
    (norm_nonneg _) (norm_nonneg _) htriangle
  have hupper := transitionCLM_quadratic_bound G hdeg x
  rw [hx] at hupper
  change ‖transitionCLM G x‖ ^ 2 ≤ (1 / 2 : ℝ) * (1 ^ 2 + r.re) at hupper
  have hresult : ‖w‖ ^ 2 - 1 / 2 ≤
      (2 * ‖w‖ + 1 / 2 + ‖w‖ / (2 * |w.im|)) * ‖y‖ := by
    have hcoef : ‖w‖ / (2 * |w.im|) = (‖w‖ / |w.im|) / 2 := by ring
    rw [hcoef]
    nlinarith
  exact hresult

theorem residual_lower_bound (hdeg : MinimumDegreeThree G) (w : ℂ) (hw : w.im ≠ 0)
    (x : EuclideanSpace ℂ G.Dart) :
    (‖w‖ ^ 2 - 1 / 2) * ‖x‖ ≤
      (2 * ‖w‖ + 1 / 2 + ‖w‖ / (2 * |w.im|)) *
        ‖transitionCLM G x - w • x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let a : ℂ := (‖x‖⁻¹ : ℝ)
  have ha : ‖a‖ = ‖x‖⁻¹ := by
    simp [a, Complex.norm_real]
  have hn : ‖a • x‖ = 1 := by rw [norm_smul, ha, inv_mul_cancel₀ hnorm.ne']
  have h := normalized_residual_lower_bound G hdeg w hw (a • x) hn
  have he : transitionCLM G (a • x) - w • (a • x) =
      a • (transitionCLM G x - w • x) := by
    rw [map_smul, smul_sub, smul_smul, smul_smul, mul_comm w a]
  rw [he, norm_smul, ha] at h
  have hm := mul_le_mul_of_nonneg_right h (norm_nonneg x)
  have hc : (‖x‖⁻¹ * ‖transitionCLM G x - w • x‖) * ‖x‖ =
      ‖transitionCLM G x - w • x‖ := by
    rw [mul_right_comm, inv_mul_cancel₀ hnorm.ne', one_mul]
  rw [mul_assoc _ (‖x‖⁻¹ * ‖transitionCLM G x - w • x‖) ‖x‖, hc] at hm
  exact hm

end GirthVerification
