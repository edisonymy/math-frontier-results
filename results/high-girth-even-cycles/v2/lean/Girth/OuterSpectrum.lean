import Girth.ComplexQuadratic

namespace GirthVerification

open scoped BigOperators

theorem sum_normSq_pos {ι : Type*} [Fintype ι] (x : ι → ℂ) (hx : x ≠ 0) :
    0 < ∑ i, Complex.normSq (x i) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  apply lt_of_lt_of_le (Complex.normSq_pos.mpr hi)
  exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (x j)) (Finset.mem_univ i)

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem eigenvector_reversal_quadratic (x : G.Dart → ℂ) (z : ℂ)
    (hPx : (complexTransition G).mulVec x = z • x) :
    complexQuadratic (reversal G * transition G) x =
      z * complexQuadratic (reversal G) x := by
  unfold complexQuadratic
  rw [complexLift_mul]
  simp_rw [← Matrix.mulVec_mulVec]
  change (∑ e, star (x e) * (complexLift (reversal G)).mulVec
    ((complexTransition G).mulVec x) e) = _
  rw [hPx]
  simp_rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem eigenvector_normSq (x : G.Dart → ℂ) (z : ℂ)
    (hPx : (complexTransition G).mulVec x = z • x) :
    (∑ e, Complex.normSq ((complexTransition G).mulVec x e)) =
      Complex.normSq z * ∑ e, Complex.normSq (x e) := by
  rw [hPx]
  simp [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]

/-- Every nonreal eigenvalue of the actual graph transition matrix satisfies
the dimension-independent squared-modulus bound in display (5). -/
theorem nonreal_eigenvalue_normSq_le_half (hdeg : MinimumDegreeThree G)
    (x : G.Dart → ℂ) (hx : x ≠ 0) (z : ℂ) (hz : z.im ≠ 0)
    (hPx : (complexTransition G).mulVec x = z • x) : Complex.normSq z ≤ 1 / 2 := by
  have hJ := reversal_quadratic_im_zero G x
  have hJP := reversal_transition_quadratic_im_zero G x
  have he := eigenvector_reversal_quadratic G x z hPx
  have him := congrArg Complex.im he
  simp only [Complex.mul_im, hJ, mul_zero, zero_add, hJP] at him
  have hJre : (complexQuadratic (reversal G) x).re = 0 :=
    (mul_eq_zero.mp him.symm).resolve_left hz
  have hJzero : complexQuadratic (reversal G) x = 0 :=
    Complex.ext hJre hJ
  have hJPzero : complexQuadratic (reversal G * transition G) x = 0 := by
    rw [he, hJzero, mul_zero]
  have hq := complexTransition_quadratic_bound G hdeg x
  rw [eigenvector_normSq G x z hPx, hJPzero] at hq
  simp only [Complex.zero_re, add_zero] at hq
  exact (mul_le_mul_iff_of_pos_right (sum_normSq_pos x hx)).mp hq

theorem real_eigenvalue_reversal_form_bound (hdeg : MinimumDegreeThree G)
    (x : G.Dart → ℂ) (z : ℝ)
    (hPx : (complexTransition G).mulVec x = (z : ℂ) • x) :
    (2 * z ^ 2 - 1) * (∑ e, Complex.normSq (x e)) ≤
      z * (complexQuadratic (reversal G) x).re := by
  have hq := complexTransition_quadratic_bound G hdeg x
  rw [eigenvector_normSq G x (z : ℂ) hPx,
    eigenvector_reversal_quadratic G x (z : ℂ) hPx] at hq
  simp only [Complex.normSq_ofReal, ← sq, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hq
  nlinarith

theorem eigenvalue_normSq_le_one (hdeg : MinimumDegreeThree G)
    (x : G.Dart → ℂ) (hx : x ≠ 0) (z : ℂ)
    (hPx : (complexTransition G).mulVec x = z • x) : Complex.normSq z ≤ 1 := by
  have h := complexTransition_normSq_contraction G hdeg x
  rw [eigenvector_normSq G x z hPx] at h
  exact (mul_le_mul_iff_of_pos_right (sum_normSq_pos x hx)).mp (by simpa using h)

theorem positive_outer_reversal_form (hdeg : MinimumDegreeThree G)
    (x : G.Dart → ℂ) (hx : x ≠ 0) (z : ℝ) (hz : 0 < z) (hzouter : 1 / 2 < z ^ 2)
    (hPx : (complexTransition G).mulVec x = (z : ℂ) • x) :
    0 < (complexQuadratic (reversal G) x).re := by
  have h := real_eigenvalue_reversal_form_bound G hdeg x z hPx
  have hleft : 0 < (2 * z ^ 2 - 1) * ∑ e, Complex.normSq (x e) :=
    mul_pos (by linarith) (sum_normSq_pos x hx)
  exact (mul_pos_iff_of_pos_left hz).mp (lt_of_lt_of_le hleft h)

theorem negative_outer_reversal_form (hdeg : MinimumDegreeThree G)
    (x : G.Dart → ℂ) (hx : x ≠ 0) (z : ℝ) (hz : z < 0) (hzouter : 1 / 2 < z ^ 2)
    (hPx : (complexTransition G).mulVec x = (z : ℂ) • x) :
    (complexQuadratic (reversal G) x).re < 0 := by
  have h := real_eigenvalue_reversal_form_bound G hdeg x z hPx
  have hleft : 0 < (2 * z ^ 2 - 1) * ∑ e, Complex.normSq (x e) :=
    mul_pos (by linarith) (sum_normSq_pos x hx)
  by_contra hs
  have hs' : 0 ≤ (complexQuadratic (reversal G) x).re := le_of_not_gt hs
  have hp := mul_nonpos_of_nonpos_of_nonneg hz.le hs'
  linarith

theorem outer_reversal_form_ne_zero (hdeg : MinimumDegreeThree G)
    (x : G.Dart → ℂ) (hx : x ≠ 0) (z : ℝ) (hzouter : 1 / 2 < z ^ 2)
    (hPx : (complexTransition G).mulVec x = (z : ℂ) • x) :
    complexQuadratic (reversal G) x ≠ 0 := by
  have h := real_eigenvalue_reversal_form_bound G hdeg x z hPx
  have hleft : 0 < (2 * z ^ 2 - 1) * ∑ e, Complex.normSq (x e) :=
    mul_pos (by linarith) (sum_normSq_pos x hx)
  intro hj
  rw [hj] at h
  simp only [Complex.zero_re, mul_zero] at h
  exact (not_le_of_gt hleft) h

end GirthVerification
