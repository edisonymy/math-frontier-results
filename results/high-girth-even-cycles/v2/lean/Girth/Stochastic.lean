import Girth.NonBacktracking
import Mathlib.Data.Complex.BigOperators

namespace GirthVerification

open scoped BigOperators

theorem weighted_square_le {ι : Type*} [Fintype ι] (p x : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (∑ i, p i * x i) ^ 2 ≤ ∑ i, p i * x i ^ 2 := by
  let s := ∑ i, p i * x i
  have hv : 0 ≤ ∑ i, p i * (x i - s) ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))
  have hid : (∑ i, p i * (x i - s) ^ 2) = (∑ i, p i * x i ^ 2) - s ^ 2 := by
    simp_rw [show ∀ i, p i * (x i - s) ^ 2 =
      p i * x i ^ 2 - 2 * s * (p i * x i) + s ^ 2 * p i by intro i; ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hs]
    dsimp [s]
    ring
  rw [hid] at hv
  dsimp [s] at hv
  linarith

theorem stochastic_square_contraction {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hp : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1) (x : ι → ℝ) :
    ∑ i, (A.mulVec x i) ^ 2 ≤ ∑ j, x j ^ 2 := by
  calc
    ∑ i, (A.mulVec x i) ^ 2 ≤ ∑ i, ∑ j, A i j * x j ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact weighted_square_le (A i) x (hp i) (hrow i)
    _ = ∑ j, x j ^ 2 := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hcol, one_mul]

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem transition_square_contraction (hdeg : MinimumDegreeThree G) (x : G.Dart → ℝ) :
    ∑ e, ((transition G).mulVec x e) ^ 2 ≤ ∑ e, x e ^ 2 :=
  stochastic_square_contraction (transition G) (transition_nonneg G)
    (transition_row_sum G hdeg) (transition_column_sum G hdeg) x

noncomputable def complexTransition : Matrix G.Dart G.Dart ℂ :=
  (transition G).map Complex.ofReal

noncomputable def complexReversal : Matrix G.Dart G.Dart ℂ :=
  (reversal G).map Complex.ofReal

theorem complexTransition_mulVec_re (x : G.Dart → ℂ) (e : G.Dart) :
    ((complexTransition G).mulVec x e).re =
      (transition G).mulVec (fun f => (x f).re) e := by
  simp [complexTransition, Matrix.mulVec, dotProduct, Complex.mul_re]

theorem complexTransition_mulVec_im (x : G.Dart → ℂ) (e : G.Dart) :
    ((complexTransition G).mulVec x e).im =
      (transition G).mulVec (fun f => (x f).im) e := by
  simp [complexTransition, Matrix.mulVec, dotProduct, Complex.mul_im]

theorem complexTransition_normSq_contraction (hdeg : MinimumDegreeThree G)
    (x : G.Dart → ℂ) :
    ∑ e, Complex.normSq ((complexTransition G).mulVec x e) ≤ ∑ e, Complex.normSq (x e) := by
  have hr := transition_square_contraction G hdeg (fun e => (x e).re)
  have hi := transition_square_contraction G hdeg (fun e => (x e).im)
  simp only [Complex.normSq_apply, ← sq, complexTransition_mulVec_re,
    complexTransition_mulVec_im, Finset.sum_add_distrib]
  linarith

end GirthVerification
