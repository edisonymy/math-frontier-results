import Girth.ComplexQuadratic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian

namespace GirthVerification

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open WithLp

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def transitionCLM :
    EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart :=
  Matrix.toEuclideanCLM (n := G.Dart) (𝕜 := ℂ) (complexTransition G)

noncomputable def reversalCLM :
    EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart :=
  Matrix.toEuclideanCLM (n := G.Dart) (𝕜 := ℂ) (complexReversal G)

noncomputable def reversalTransitionCLM :
    EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart :=
  Matrix.toEuclideanCLM (n := G.Dart) (𝕜 := ℂ) (complexLift (reversal G * transition G))

theorem transitionCLM_apply (x : EuclideanSpace ℂ G.Dart) (e : G.Dart) :
    transitionCLM G x e = (complexTransition G).mulVec (ofLp x) e := rfl

theorem reversalCLM_apply (x : EuclideanSpace ℂ G.Dart) (e : G.Dart) :
    reversalCLM G x e = x e.symm := by
  classical
  simp [reversalCLM, Matrix.ofLp_toEuclideanCLM, complexReversal,
    Matrix.mulVec, dotProduct, reversal, apply_ite]

theorem reversalCLM_norm (x : EuclideanSpace ℂ G.Dart) : ‖reversalCLM G x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, reversalCLM_apply]
  exact (reverseEquiv G).sum_comp (fun e => ‖x e‖ ^ 2)

theorem reversalCLM_sq_apply (x : EuclideanSpace ℂ G.Dart) :
    reversalCLM G (reversalCLM G x) = x := by
  ext e
  simp [reversalCLM_apply]

theorem transitionCLM_norm_le_one (hdeg : MinimumDegreeThree G) : ‖transitionCLM G‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, transitionCLM_apply]
  simpa only [Complex.normSq_eq_norm_sq] using
    complexTransition_normSq_contraction G hdeg (ofLp x)

theorem complexTransition_operator_norm_le_one (hdeg : MinimumDegreeThree G) :
    ‖complexTransition G‖ ≤ 1 := transitionCLM_norm_le_one G hdeg

theorem reversalTransitionCLM_eq_comp :
    reversalTransitionCLM G = (reversalCLM G).comp (transitionCLM G) := by
  unfold reversalTransitionCLM
  rw [complexLift_mul, map_mul]
  rfl

theorem reversalTransitionCLM_isSymmetric :
    (reversalTransitionCLM G : Module.End ℂ (EuclideanSpace ℂ G.Dart)).IsSymmetric :=
  Matrix.isHermitian_iff_isSymmetric.mp
    (complexLift_isHermitian _ (reversal_mul_transition_isHermitian G))

theorem reversalCLM_isSymmetric :
    (reversalCLM G : Module.End ℂ (EuclideanSpace ℂ G.Dart)).IsSymmetric :=
  Matrix.isHermitian_iff_isSymmetric.mp (complexLift_isHermitian _ (reversal_isHermitian G))

theorem euclidean_quadratic_eq (A : Matrix G.Dart G.Dart ℝ) (x : EuclideanSpace ℂ G.Dart) :
    ⟪x, Matrix.toEuclideanCLM (n := G.Dart) (𝕜 := ℂ) (complexLift A) x⟫_ℂ =
      complexQuadratic A (ofLp x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
  rw [dotProduct_comm]
  rfl

theorem transitionCLM_quadratic_bound (hdeg : MinimumDegreeThree G)
    (x : EuclideanSpace ℂ G.Dart) :
    ‖transitionCLM G x‖ ^ 2 ≤ (1 / 2 : ℝ) *
      (‖x‖ ^ 2 + (⟪x, reversalCLM G (transitionCLM G x)⟫_ℂ).re) := by
  rw [← ContinuousLinearMap.comp_apply, ← reversalTransitionCLM_eq_comp]
  have h := complexTransition_quadratic_bound G hdeg (ofLp x)
  change ‖transitionCLM G x‖ ^ 2 ≤ (1 / 2 : ℝ) *
    (‖x‖ ^ 2 + (⟪x, Matrix.toEuclideanCLM (n := G.Dart) (𝕜 := ℂ)
      (complexLift (reversal G * transition G)) x⟫_ℂ).re)
  rw [euclidean_quadratic_eq]
  simpa only [EuclideanSpace.norm_sq_eq, transitionCLM_apply,
    ← Complex.normSq_eq_norm_sq] using h

end GirthVerification
