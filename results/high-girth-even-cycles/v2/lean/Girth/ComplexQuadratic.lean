import Girth.Stochastic
import Girth.ReversalBound

namespace GirthVerification

open scoped BigOperators

noncomputable def complexLift {ι : Type*} (A : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  A.map (Complex.ofRealHom : ℝ → ℂ)

noncomputable def complexQuadratic {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x : ι → ℂ) : ℂ :=
  ∑ i, star (x i) * (complexLift A).mulVec x i

theorem complexLift_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) :
    complexLift (A * B) = complexLift A * complexLift B := Matrix.map_mul

theorem complexLift_mulVec_re {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x : ι → ℂ) (i : ι) :
    ((complexLift A).mulVec x i).re = A.mulVec (fun j => (x j).re) i := by
  simp [complexLift, Matrix.mulVec, dotProduct, Complex.mul_re]

theorem complexLift_mulVec_im {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x : ι → ℂ) (i : ι) :
    ((complexLift A).mulVec x i).im = A.mulVec (fun j => (x j).im) i := by
  simp [complexLift, Matrix.mulVec, dotProduct, Complex.mul_im]

theorem complexQuadratic_re {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x : ι → ℂ) :
    (complexQuadratic A x).re =
      (∑ i, (x i).re * A.mulVec (fun j => (x j).re) i) +
      ∑ i, (x i).im * A.mulVec (fun j => (x j).im) i := by
  simp [complexQuadratic, Complex.mul_re, complexLift_mulVec_re, complexLift_mulVec_im,
    Finset.sum_add_distrib]

theorem symmetric_bilinear {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (x y : ι → ℝ) :
    ∑ i, x i * A.mulVec y i = ∑ i, y i * A.mulVec x i := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : A j i = A i j := by simpa using hA.apply i j
  rw [h]
  ring

theorem complexQuadratic_im_zero {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (x : ι → ℂ) :
    (complexQuadratic A x).im = 0 := by
  have h := symmetric_bilinear A hA (fun i => (x i).re) (fun i => (x i).im)
  simp [complexQuadratic, Complex.mul_im, complexLift_mulVec_re, complexLift_mulVec_im,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, h]

theorem complexLift_isHermitian {ι : Type*} (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    (complexLift A).IsHermitian := by
  apply hA.map
  intro r
  simp

theorem hermitian_pairing_transfer {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (x y : ι → ℂ) :
    (∑ i, star (x i) * (complexLift A).mulVec y i) =
      ∑ i, star ((complexLift A).mulVec x i) * y i := by
  change star x ⬝ᵥ (complexLift A).mulVec y = star ((complexLift A).mulVec x) ⬝ᵥ y
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, (complexLift_isHermitian A hA).eq]

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem complexTransition_quadratic_bound (hdeg : MinimumDegreeThree G) (x : G.Dart → ℂ) :
    ∑ e, Complex.normSq ((complexTransition G).mulVec x e) ≤ (1 / 2 : ℝ) *
      ((∑ e, Complex.normSq (x e)) + (complexQuadratic (reversal G * transition G) x).re) := by
  have hr := transition_quadratic_bound G hdeg (fun e => (x e).re)
  have hi := transition_quadratic_bound G hdeg (fun e => (x e).im)
  simp only [Complex.normSq_apply, ← sq, complexTransition_mulVec_re,
    complexTransition_mulVec_im, Finset.sum_add_distrib, complexQuadratic_re]
  linarith

theorem reversal_quadratic_im_zero (x : G.Dart → ℂ) :
    (complexQuadratic (reversal G) x).im = 0 :=
  complexQuadratic_im_zero _ (reversal_isHermitian G) x

theorem reversal_transition_quadratic_im_zero (x : G.Dart → ℂ) :
    (complexQuadratic (reversal G * transition G) x).im = 0 :=
  complexQuadratic_im_zero _ (reversal_mul_transition_isHermitian G) x

end GirthVerification
