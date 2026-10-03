import Girth.ModeMoments
import Mathlib.LinearAlgebra.Trace

namespace GirthVerification

open scoped InnerProductSpace
open WithLp

theorem norm_trace_clm_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (T : H →L[ℂ] H) :
    ‖LinearMap.trace ℂ H T.toLinearMap‖ ≤ (Module.finrank ℂ H : ℝ) * ‖T‖ := by
  classical
  let b := stdOrthonormalBasis ℂ H
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis]
  unfold Matrix.trace
  calc
    _ ≤ ∑ i, ‖(LinearMap.toMatrix b.toBasis b.toBasis T.toLinearMap) i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℂ H), ‖T‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply]
      calc
        _ ≤ ‖b i‖ * ‖T (b i)‖ := norm_inner_le_norm _ _
        _ ≤ ‖b i‖ * (‖T‖ * ‖b i‖) := mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
        _ = ‖T‖ := by simp [b.orthonormal.norm_eq_one]
    _ = _ := by simp [nsmul_eq_mul]

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem transitionEnd_pow_slowVector (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (i : SlowModes G c) (n : ℕ) :
    (transitionEnd G ^ n) (slowVector G hdeg c hc hcouter i) =
      (slowValue G c i : ℂ) ^ n • slowVector G hdeg c hc hcouter i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul]
    change (slowValue G c i : ℂ) ^ n •
      ((complexTransition G).mulVec (slowVector G hdeg c hc hcouter i)) = _
    rw [slowVector_eigen, smul_smul, pow_succ]

theorem transitionEnd_pow_slowProjector_eq_sum (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (n : ℕ) :
    transitionEnd G ^ n * slowProjector G hdeg c hc hcouter =
      ∑ i : SlowModes G c, (slowValue G c i : ℂ) ^ n •
        (slowCoordinate G hdeg c hc hcouter i).smulRight (slowVector G hdeg c hc hcouter i) := by
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, slowProjector_apply, map_sum, map_smul,
    transitionEnd_pow_slowVector, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

theorem trace_transitionEnd_slowProjector (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (n : ℕ) :
    LinearMap.trace ℂ (G.Dart → ℂ) (transitionEnd G ^ n * slowProjector G hdeg c hc hcouter) =
      ∑ i : SlowModes G c, (slowValue G c i : ℂ) ^ n := by
  rw [transitionEnd_pow_slowProjector_eq_sum, map_sum]
  simp only [map_smul, LinearMap.trace_smulRight, slowCoordinate_basis, if_true, smul_eq_mul, mul_one]

theorem euclideanEndLift_trace (T : Module.End ℂ (G.Dart → ℂ)) :
    LinearMap.trace ℂ (EuclideanSpace ℂ G.Dart) (euclideanEndLift G T).toLinearMap =
      LinearMap.trace ℂ (G.Dart → ℂ) T := by
  exact LinearMap.trace_conj' T (WithLp.linearEquiv 2 ℂ (G.Dart → ℂ)).symm

theorem euclideanEndLift_pow (T : Module.End ℂ (G.Dart → ℂ)) (n : ℕ) :
    euclideanEndLift G (T ^ n) = euclideanEndLift G T ^ n := by
  induction n with
  | zero => simpa [ContinuousLinearMap.one_def] using euclideanEndLift_one G
  | succ n ih => rw [pow_succ, euclideanEndLift_mul, ih, pow_succ]

theorem trace_residual_abs_bound (hdeg : MinimumDegreeThree G) (c b : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (hcb : c < b) (hb : b < 1) (n : ℕ) :
    ‖LinearMap.trace ℂ (G.Dart → ℂ) (transitionEnd G ^ n * residualProjector G hdeg c hc hcouter)‖ ≤
      (2 * G.edgeFinset.card : ℝ) *
        ((2 * b * remainderConstant c b / cutoffRadius c b) * b ^ n) := by
  rw [← euclideanEndLift_trace G, euclideanEndLift_mul, euclideanEndLift_pow,
    euclideanEndLift_transition]
  have h := norm_trace_clm_le
    (transitionCLM G ^ n * residualProjectorCLM G hdeg c hc hcouter)
  simp only [finrank_euclideanSpace, G.dart_card_eq_twice_card_edges, Nat.cast_mul, Nat.cast_ofNat] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (residual_power_norm_bound G hdeg c b hc hcouter hcb hb n) (by positivity))

theorem trace_transitionEnd_pow_eq_real_trace (n : ℕ) :
    LinearMap.trace ℂ (G.Dart → ℂ) (transitionEnd G ^ n) = (Matrix.trace (transition G ^ n) : ℝ) := by
  rw [transitionEnd, ← Matrix.toLin'_pow, Matrix.trace_toLin'_eq]
  change Matrix.trace (complexLift (transition G) ^ n) = _
  unfold complexLift
  rw [← Matrix.map_pow]
  simp [Matrix.trace, Complex.ofReal_sum]

/-- An alternative to the algebraic-multiplicity trace calculation: the
residual power estimate gives a sufficient `N K b^L` error directly. -/
theorem even_trace_lower_bound (hdeg : MinimumDegreeThree G) (c b : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (hcb : c < b) (hb : b < 1)
    (L : ℕ) (hEven : Even L) :
    slowMoment G c L - (2 * G.edgeFinset.card : ℝ) *
      ((2 * b * remainderConstant c b / cutoffRadius c b) * b ^ L) ≤
        Matrix.trace (transition G ^ L) := by
  have hsplit : transitionEnd G ^ L =
      transitionEnd G ^ L * slowProjector G hdeg c hc hcouter +
      transitionEnd G ^ L * residualProjector G hdeg c hc hcouter := by
    rw [residualProjector, mul_sub, mul_one]
    abel
  have hh := congrArg (LinearMap.trace ℂ (G.Dart → ℂ)) hsplit
  rw [trace_transitionEnd_pow_eq_real_trace, map_add, trace_transitionEnd_slowProjector] at hh
  have hslow : (∑ i : SlowModes G c, (slowValue G c i : ℂ) ^ L) = (slowMoment G c L : ℝ) := by
    simp only [slowMoment, Complex.ofReal_sum, Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Complex.ofReal_pow] using
      congrArg Complex.ofReal (hEven.pow_abs (slowValue G c i)).symm
  rw [hslow] at hh
  have hbound := trace_residual_abs_bound G hdeg c b hc hcouter hcb hb L
  have hre := Complex.abs_re_le_norm
    (LinearMap.trace ℂ (G.Dart → ℂ) (transitionEnd G ^ L * residualProjector G hdeg c hc hcouter))
  have heq := congrArg Complex.re hh
  simp only [Complex.ofReal_re, Complex.add_re] at heq
  have hneg := neg_le_abs
    (LinearMap.trace ℂ (G.Dart → ℂ) (transitionEnd G ^ L * residualProjector G hdeg c hc hcouter)).re
  linarith

end GirthVerification
