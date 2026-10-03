import Girth.ResidualSpectrum
import Girth.EuclideanOperator

namespace GirthVerification

open WithLp

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def euclideanEndLift (T : Module.End ℂ (G.Dart → ℂ)) :
    EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart :=
  LinearMap.toContinuousLinearMap (𝕜 := ℂ) ((WithLp.linearEquiv 2 ℂ (G.Dart → ℂ)).symm.conj T)

omit [DecidableEq V] in
theorem euclideanEndLift_apply (T : Module.End ℂ (G.Dart → ℂ)) (x : EuclideanSpace ℂ G.Dart) :
    euclideanEndLift G T x = toLp 2 (T (ofLp x)) := rfl

omit [DecidableEq V] in
theorem euclideanEndLift_mul (T U : Module.End ℂ (G.Dart → ℂ)) :
    euclideanEndLift G (T * U) = euclideanEndLift G T * euclideanEndLift G U := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

omit [DecidableEq V] in
theorem euclideanEndLift_sub (T U : Module.End ℂ (G.Dart → ℂ)) :
    euclideanEndLift G (T - U) = euclideanEndLift G T - euclideanEndLift G U := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

omit [DecidableEq V] in
theorem euclideanEndLift_one :
    euclideanEndLift G 1 = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ G.Dart) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem euclideanEndLift_transition : euclideanEndLift G (transitionEnd G) = transitionCLM G := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

noncomputable def slowProjectorCLM (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart :=
  euclideanEndLift G (slowProjector G hdeg c hc hcouter)

noncomputable def residualProjectorCLM (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart :=
  euclideanEndLift G (residualProjector G hdeg c hc hcouter)

theorem residualProjectorCLM_eq_sub (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    residualProjectorCLM G hdeg c hc hcouter = ContinuousLinearMap.id ℂ _ -
      slowProjectorCLM G hdeg c hc hcouter := by
  rw [residualProjectorCLM, residualProjector, euclideanEndLift_sub, euclideanEndLift_one]
  rfl

theorem residualProjectorCLM_idempotent (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    residualProjectorCLM G hdeg c hc hcouter * residualProjectorCLM G hdeg c hc hcouter =
      residualProjectorCLM G hdeg c hc hcouter := by
  rw [residualProjectorCLM, ← euclideanEndLift_mul, residualProjector_idempotent]

theorem residualProjectorCLM_commutes (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    transitionCLM G * residualProjectorCLM G hdeg c hc hcouter =
      residualProjectorCLM G hdeg c hc hcouter * transitionCLM G := by
  rw [residualProjectorCLM, ← euclideanEndLift_transition, ← euclideanEndLift_mul,
    ← euclideanEndLift_mul, residualProjector_commutes]

end GirthVerification
