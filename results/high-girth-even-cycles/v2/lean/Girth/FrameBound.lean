import Girth.EuclideanOperator

namespace GirthVerification

open scoped BigOperators InnerProductSpace
open WithLp

noncomputable def modeScale {ι : Type*} [Fintype ι] (z : ι → ℝ)
    (u : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  toLp 2 (fun i => (z i : ℂ) * u i)

noncomputable def modeInverse {ι : Type*} [Fintype ι] (z : ι → ℝ)
    (u : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  toLp 2 (fun i => ((z i)⁻¹ : ℝ) * u i)

theorem modeScale_inverse {ι : Type*} [Fintype ι] (z : ι → ℝ)
    (hz : ∀ i, z i ≠ 0) (u : EuclideanSpace ℂ ι) :
    modeScale z (modeInverse z u) = u := by
  ext i
  simp [modeScale, modeInverse, ← mul_assoc, hz i]

theorem modeInverse_norm_le {ι : Type*} [Fintype ι] (z : ι → ℝ)
    (c : ℝ) (hc : 0 < c) (hz : ∀ i, c ≤ z i) (u : EuclideanSpace ℂ ι) :
    ‖modeInverse z u‖ ≤ ‖u‖ / c := by
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) hc.le)).mp
  rw [EuclideanSpace.norm_sq_eq, div_pow, EuclideanSpace.norm_sq_eq]
  calc
    _ = ∑ i, (‖u i‖ / z i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [modeInverse, Complex.norm_real, abs_of_pos (lt_of_lt_of_le hc (hz i)),
        div_eq_mul_inv, mul_comm]
    _ ≤ ∑ i, (‖u i‖ / c) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply (sq_le_sq₀ (div_nonneg (norm_nonneg _) (hc.trans_le (hz i)).le)
        (div_nonneg (norm_nonneg _) hc.le)).mpr
      exact div_le_div_of_nonneg_left (norm_nonneg _) hc (hz i)
    _ = _ := by simp_rw [div_pow]; rw [Finset.sum_div]

theorem modeInverse_inner_re_le {ι : Type*} [Fintype ι] (z : ι → ℝ)
    (c : ℝ) (hc : 0 < c) (hz : ∀ i, c ≤ z i) (u : EuclideanSpace ℂ ι) :
    (⟪modeInverse z u, u⟫_ℂ).re ≤ ‖u‖ ^ 2 / c := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  have he : ∀ i, (u i * star (modeInverse z u i)).re = (z i)⁻¹ * Complex.normSq (u i) := by
    intro i
    simp [modeInverse, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
    ring
  change (∑ i, u i * star (modeInverse z u i)).re ≤ _
  simp only [Complex.re_sum, he]
  calc
    _ ≤ ∑ i, c⁻¹ * Complex.normSq (u i) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg _)
      simpa only [one_div] using one_div_le_one_div_of_le hc (hz i)
    _ = _ := by rw [← Finset.mul_sum]; simp [Complex.normSq_eq_norm_sq,
        EuclideanSpace.norm_sq_eq, div_eq_mul_inv, mul_comm]

theorem opNorm_sq_le_of_sq_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (T : E →L[ℂ] F) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ x, ‖T x‖ ^ 2 ≤ M * ‖x‖ ^ 2) : ‖T‖ ^ 2 ≤ M := by
  have hnorm : ‖T‖ ≤ Real.sqrt M := by
    apply T.opNorm_le_bound (Real.sqrt_nonneg M)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hM]
    exact h x
  have hsq := (sq_le_sq₀ (norm_nonneg T) (Real.sqrt_nonneg M)).mpr hnorm
  rwa [Real.sq_sqrt hM] at hsq

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Dimension-independent bound for any normalized single-sign outer
eigenframe of the actual graph operator. Its eigenvectors and normalization
are explicit premises; the frame estimate itself is proved here. -/
theorem single_sign_eigenframe_norm_sq_le (hdeg : MinimumDegreeThree G)
    {ι : Type*} [Fintype ι] (F : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ G.Dart)
    (z : ι → ℝ) (s c : ℝ) (hs : s = 1 ∨ s = -1) (hc : 0 < c)
    (hcouter : 1 / 2 < c ^ 2) (hz : ∀ i, c ≤ z i)
    (hEigen : ∀ u, transitionCLM G (F u) = (s : ℂ) • F (modeScale z u))
    (hFrame : ∀ u v, ⟪F u, reversalCLM G (F v)⟫_ℂ = (s : ℂ) * ⟪u, v⟫_ℂ) :
    ‖F‖ ^ 2 ≤ c / (2 * c ^ 2 - 1) := by
  have hsnorm : ‖(s : ℂ)‖ = 1 := by rcases hs with rfl | rfl <;> simp
  have hss : (s : ℂ) * (s : ℂ) = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hz0 : ∀ i, z i ≠ 0 := fun i => (hc.trans_le (hz i)).ne'
  have htest : ∀ u : EuclideanSpace ℂ ι, ‖F u‖ ^ 2 ≤
      (1 / 2 : ℝ) * (‖F (modeInverse z u)‖ ^ 2 + (⟪modeInverse z u, u⟫_ℂ).re) := by
    intro u
    have h := transitionCLM_quadratic_bound G hdeg (F (modeInverse z u))
    rw [hEigen, modeScale_inverse z hz0, norm_smul, hsnorm, one_mul,
      map_smul, inner_smul_right, hFrame, ← mul_assoc, hss, one_mul] at h
    exact h
  have hpoint : ∀ u : EuclideanSpace ℂ ι,
      ‖F u‖ ^ 2 ≤ (1 / 2 : ℝ) * (‖F‖ ^ 2 / c ^ 2 + 1 / c) * ‖u‖ ^ 2 := by
    intro u
    have hnorm : ‖F (modeInverse z u)‖ ≤ ‖F‖ * (‖u‖ / c) :=
      (F.le_opNorm _).trans (mul_le_mul_of_nonneg_left (modeInverse_norm_le z c hc hz u)
        (norm_nonneg F))
    have hnormsq := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg F) (div_nonneg (norm_nonneg u) hc.le))).mpr hnorm
    have hinner := modeInverse_inner_re_le z c hc hz u
    calc
      _ ≤ (1 / 2 : ℝ) * ((‖F‖ * (‖u‖ / c)) ^ 2 + ‖u‖ ^ 2 / c) := by
        exact (htest u).trans (mul_le_mul_of_nonneg_left (add_le_add hnormsq hinner) (by norm_num))
      _ = _ := by ring
  have hnorm := opNorm_sq_le_of_sq_bound F
    ((1 / 2 : ℝ) * (‖F‖ ^ 2 / c ^ 2 + 1 / c)) (by positivity) hpoint
  have hd : 0 < 2 * c ^ 2 - 1 := by linarith
  apply (le_div_iff₀ hd).mpr
  have ht : (1 / 2 : ℝ) * (‖F‖ ^ 2 / c ^ 2 + 1 / c) =
      (‖F‖ ^ 2 + c) / (2 * c ^ 2) := by field_simp
  rw [ht] at hnorm
  have hp := (le_div_iff₀ (by positivity : 0 < 2 * c ^ 2)).mp hnorm
  nlinarith

end GirthVerification
