import Girth.SlowModes

namespace GirthVerification

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def slowCoordinate (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (i : SlowModes G c) : (G.Dart → ℂ) →ₗ[ℂ] ℂ where
  toFun x := (eigenSign (slowValue G c i) : ℂ) *
    reversalPairing G (slowVector G hdeg c hc hcouter i) x
  map_add' x y := by rw [reversalPairing_add_right, mul_add]
  map_smul' z x := by
    rw [reversalPairing_smul_right]
    change _ = z * _
    ring

theorem slowCoordinate_apply (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (i : SlowModes G c) (x : G.Dart → ℂ) :
    slowCoordinate G hdeg c hc hcouter i x = (eigenSign (slowValue G c i) : ℂ) *
      reversalPairing G (slowVector G hdeg c hc hcouter i) x := rfl

theorem slowCoordinate_basis (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (i j : SlowModes G c) :
    slowCoordinate G hdeg c hc hcouter i (slowVector G hdeg c hc hcouter j) =
      if i = j then 1 else 0 := by
  classical
  rw [slowCoordinate_apply, slowVector_pairing]
  by_cases h : i = j
  · subst j
    rcases eigenSign_cases (slowValue G c i) with hs | hs <;> simp [hs]
  · simp [h]

noncomputable def slowProjector (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) : Module.End ℂ (G.Dart → ℂ) where
  toFun x := ∑ i, slowCoordinate G hdeg c hc hcouter i x • slowVector G hdeg c hc hcouter i
  map_add' x y := by simp only [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' z x := by simp [smul_smul, Finset.smul_sum]

theorem slowProjector_apply (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (x : G.Dart → ℂ) :
    slowProjector G hdeg c hc hcouter x =
      ∑ i, slowCoordinate G hdeg c hc hcouter i x • slowVector G hdeg c hc hcouter i := rfl

theorem slowProjector_basis (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (i : SlowModes G c) :
    slowProjector G hdeg c hc hcouter (slowVector G hdeg c hc hcouter i) =
      slowVector G hdeg c hc hcouter i := by
  simp [slowProjector_apply, slowCoordinate_basis, eq_comm, ite_smul]

theorem slowProjector_idempotent (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    (slowProjector G hdeg c hc hcouter).comp (slowProjector G hdeg c hc hcouter) =
      slowProjector G hdeg c hc hcouter := by
  apply LinearMap.ext
  intro x
  change slowProjector G hdeg c hc hcouter (slowProjector G hdeg c hc hcouter x) = _
  rw [slowProjector_apply G hdeg c hc hcouter x, map_sum]
  simp only [map_smul, slowProjector_basis]

theorem slowCoordinate_eigen_left (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (i : SlowModes G c) (x : G.Dart → ℂ) :
    slowCoordinate G hdeg c hc hcouter i ((transitionEnd G) x) =
      (slowValue G c i : ℂ) * slowCoordinate G hdeg c hc hcouter i x := by
  rw [slowCoordinate_apply, slowCoordinate_apply]
  change (eigenSign (slowValue G c i) : ℂ) * reversalPairing G
    (slowVector G hdeg c hc hcouter i) ((complexTransition G).mulVec x) = _
  rw [reversalPairing_eigen_left G _ _ (slowVector_eigen G hdeg c hc hcouter i)]
  ring

theorem slowProjector_commutes (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    (transitionEnd G).comp (slowProjector G hdeg c hc hcouter) =
      (slowProjector G hdeg c hc hcouter).comp (transitionEnd G) := by
  apply LinearMap.ext
  intro x
  change transitionEnd G (slowProjector G hdeg c hc hcouter x) =
    slowProjector G hdeg c hc hcouter (transitionEnd G x)
  rw [slowProjector_apply, map_sum, slowProjector_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, slowCoordinate_eigen_left]
  change slowCoordinate G hdeg c hc hcouter i x •
    ((complexTransition G).mulVec (slowVector G hdeg c hc hcouter i)) = _
  rw [slowVector_eigen, smul_smul]
  simp [mul_comm]

theorem slowCoordinate_generalized_zero (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (i : SlowModes G c) (w : ℂ)
    (hiw : (slowValue G c i : ℂ) ≠ w) (n : ℕ) (x : G.Dart → ℂ)
    (hx : ((transitionEnd G - w • 1) ^ n) x = 0) : slowCoordinate G hdeg c hc hcouter i x = 0 := by
  rw [slowCoordinate_apply, eigenvector_generalized_reversal_orthogonal G _ _ w hiw
    (slowVector_eigen G hdeg c hc hcouter i) n x hx, mul_zero]

theorem slowProjector_inner_generalized_zero (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) (hw : ‖w‖ ≤ c)
    (n : ℕ) (x : G.Dart → ℂ) (hx : ((transitionEnd G - w • 1) ^ n) x = 0) :
    slowProjector G hdeg c hc hcouter x = 0 := by
  rw [slowProjector_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hiw : (slowValue G c i : ℂ) ≠ w := by
    intro heq
    rw [← heq, Complex.norm_real] at hw
    exact (not_le_of_gt i.1.property.2) hw
  rw [slowCoordinate_generalized_zero G hdeg c hc hcouter i w hiw n x hx, zero_smul]

theorem slowProjector_outer_identity (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (z : outerRealEigenvalues G c)
    (x : outerEigenspace G z.val) :
    slowProjector G hdeg c hc hcouter x.val = x.val := by
  classical
  let b := normalizedOuterBasis G hdeg c hc hcouter z
  have hx := congrArg Subtype.val (b.sum_repr x)
  have hx' : (∑ i, b.repr x i • slowVector G hdeg c hc hcouter ⟨z, i⟩) = x.val := by
    simpa only [b, slowVector, Submodule.coe_sum, Submodule.coe_smul] using hx
  rw [← hx', map_sum]
  simp only [map_smul, slowProjector_basis]

end GirthVerification
