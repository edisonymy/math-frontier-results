import Girth.SlowResolvent

namespace GirthVerification

open scoped BigOperators InnerProductSpace
open WithLp

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem signFrame_single (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (s : ℝ) (i : SignedSlowModes G c s) :
    signFrame G hdeg c hc hcouter s (toLp 2 (Pi.single i (1 : ℂ))) =
      toLp 2 (slowVector G hdeg c hc hcouter i.val) := by
  classical
  simp [signFrame_apply, ite_smul]

theorem signFrame_adjoint_coordinate (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (s : ℝ) (i : SignedSlowModes G c s)
    (x : EuclideanSpace ℂ G.Dart) :
    (signFrame G hdeg c hc hcouter s).adjoint x i =
      ⟪toLp 2 (slowVector G hdeg c hc hcouter i.val), x⟫_ℂ := by
  classical
  calc
    _ = ⟪toLp 2 (Pi.single i (1 : ℂ)), (signFrame G hdeg c hc hcouter s).adjoint x⟫_ℂ := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.single_apply]
    _ = ⟪signFrame G hdeg c hc hcouter s (toLp 2 (Pi.single i (1 : ℂ))), x⟫_ℂ :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = _ := by rw [signFrame_single]

theorem modeResolvent_apply (c s : ℝ) (w : ℂ)
    (u : EuclideanSpace ℂ (SignedSlowModes G c s)) (i : SignedSlowModes G c s) :
    modeResolvent G c s w u i = (1 / (w - (slowValue G c i.val : ℂ))) * u i := by
  change (Matrix.diagonal (fun j => 1 / (w - (slowValue G c j.val : ℂ)))).mulVec (ofLp u) i = _
  rw [Matrix.mulVec_diagonal]

theorem signedSlowResolvent_formula (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (s : ℝ) (w : ℂ)
    (x : EuclideanSpace ℂ G.Dart) :
    signedSlowResolvent G hdeg c hc hcouter s w x =
      ∑ i : SignedSlowModes G c s,
        ((1 / (w - (slowValue G c i.val : ℂ))) *
          slowCoordinate G hdeg c hc hcouter i.val (ofLp x)) •
            toLp 2 (slowVector G hdeg c hc hcouter i.val) := by
  rw [signedSlowResolvent, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, signFrame_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [modeResolvent_apply, signFrame_adjoint_coordinate, smul_smul, slowCoordinate_apply]
  have hp : ⟪toLp 2 (slowVector G hdeg c hc hcouter i.val), reversalCLM G x⟫_ℂ =
      reversalPairing G (slowVector G hdeg c hc hcouter i.val) (ofLp x) :=
    euclidean_reversalPairing_eq G _ (ofLp x)
  rw [hp]
  have hs : eigenSign (slowValue G c i.val) = s := i.property
  simp only [hs]
  congr 1
  ring

theorem sum_signed_modes {M : Type*} [AddCommMonoid M] (c : ℝ) (f : SlowModes G c → M) :
    (∑ i : SignedSlowModes G c 1, f i.val) +
      (∑ i : SignedSlowModes G c (-1), f i.val) = ∑ i, f i := by
  classical
  let p := fun i : SlowModes G c => eigenSign (slowValue G c i) = 1
  have hneg : ∀ i : SlowModes G c, eigenSign (slowValue G c i) = -1 ↔ ¬ p i := by
    intro i
    rcases eigenSign_cases (slowValue G c i) with hs | hs <;> norm_num [p, hs]
  let he : SignedSlowModes G c (-1) ≃ {i : SlowModes G c // ¬ p i} :=
    { toFun := fun i => ⟨i.val, (hneg i.val).mp i.property⟩
      invFun := fun i => ⟨i.val, (hneg i.val).mpr i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsum : (∑ i : SignedSlowModes G c (-1), f i.val) = ∑ i : {i // ¬ p i}, f i.val :=
    Fintype.sum_equiv he _ _ (fun _ => rfl)
  rw [hsum]
  exact Fintype.sum_subtype_add_sum_subtype p f

/-- The bounded frame resolvent is exactly the normalized slow projector
sum, not an abstract operator unrelated to the graph's eigenspaces. -/
theorem fullSlowResolvent_formula (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) (x : EuclideanSpace ℂ G.Dart) :
    fullSlowResolvent G hdeg c hc hcouter w x =
      ∑ i : SlowModes G c,
        ((1 / (w - (slowValue G c i : ℂ))) * slowCoordinate G hdeg c hc hcouter i (ofLp x)) •
          toLp 2 (slowVector G hdeg c hc hcouter i) := by
  rw [fullSlowResolvent, ContinuousLinearMap.add_apply, signedSlowResolvent_formula,
    signedSlowResolvent_formula]
  exact sum_signed_modes (M := EuclideanSpace ℂ G.Dart) G c
    (fun i => ((1 / (w - (slowValue G c i : ℂ))) *
      slowCoordinate G hdeg c hc hcouter i (ofLp x)) • toLp 2 (slowVector G hdeg c hc hcouter i))

end GirthVerification
