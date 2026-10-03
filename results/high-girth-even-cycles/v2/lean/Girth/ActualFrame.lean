import Girth.SlowModes
import Girth.FrameBound

namespace GirthVerification

open scoped BigOperators InnerProductSpace
open WithLp

theorem eigenSign_mul_abs (z : ℝ) : eigenSign z * |z| = z := by
  classical
  by_cases h : 0 ≤ z
  · simp [eigenSign, h, abs_of_nonneg h]
  · simp [eigenSign, h, abs_of_neg (lt_of_not_ge h)]

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def SignedSlowModes (c s : ℝ) : Type := {i : SlowModes G c // eigenSign (slowValue G c i) = s}

noncomputable instance (c s : ℝ) : Fintype (SignedSlowModes G c s) := by
  classical
  unfold SignedSlowModes
  infer_instance

noncomputable instance (c s : ℝ) : DecidableEq (SignedSlowModes G c s) := Classical.decEq _

noncomputable def signFrameLinear (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (s : ℝ) :
    EuclideanSpace ℂ (SignedSlowModes G c s) →ₗ[ℂ] EuclideanSpace ℂ G.Dart where
  toFun u := ∑ i, u i • toLp 2 (slowVector G hdeg c hc hcouter i.val)
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z u := by simp [smul_smul, Finset.smul_sum]

noncomputable def signFrame (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (s : ℝ) :
    EuclideanSpace ℂ (SignedSlowModes G c s) →L[ℂ] EuclideanSpace ℂ G.Dart :=
  (signFrameLinear G hdeg c hc hcouter s).toContinuousLinearMap

theorem signFrame_apply (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (s : ℝ)
    (u : EuclideanSpace ℂ (SignedSlowModes G c s)) :
    signFrame G hdeg c hc hcouter s u =
      ∑ i, u i • toLp 2 (slowVector G hdeg c hc hcouter i.val) := rfl

theorem euclidean_reversalPairing_eq (x y : G.Dart → ℂ) :
    ⟪toLp 2 x, reversalCLM G (toLp 2 y)⟫_ℂ = reversalPairing G x y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (complexLift (reversal G)).mulVec y ⬝ᵥ star x =
    star x ⬝ᵥ (complexLift (reversal G)).mulVec y
  exact dotProduct_comm _ _

theorem signFrame_basis_pairing (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (s : ℝ) (i j : SignedSlowModes G c s) :
    ⟪toLp 2 (slowVector G hdeg c hc hcouter i.val),
      reversalCLM G (toLp 2 (slowVector G hdeg c hc hcouter j.val))⟫_ℂ =
        (s : ℂ) * if i = j then 1 else 0 := by
  rw [euclidean_reversalPairing_eq, slowVector_pairing, i.property]
  have heq : i.val = j.val ↔ i = j := ⟨Subtype.ext, congrArg Subtype.val⟩
  simp only [heq]

theorem signFrame_eigen (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (s : ℝ)
    (u : EuclideanSpace ℂ (SignedSlowModes G c s)) :
    transitionCLM G (signFrame G hdeg c hc hcouter s u) =
      (s : ℂ) • signFrame G hdeg c hc hcouter s
        (modeScale (fun i => |slowValue G c i.val|) u) := by
  rw [signFrame_apply, map_sum, signFrame_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  have he : transitionCLM G (toLp 2 (slowVector G hdeg c hc hcouter i.val)) =
      (slowValue G c i.val : ℂ) • toLp 2 (slowVector G hdeg c hc hcouter i.val) := by
    ext e
    exact congrFun (slowVector_eigen G hdeg c hc hcouter i.val) e
  rw [he]
  have hval : s * |slowValue G c i.val| = slowValue G c i.val := by
    calc
      _ = eigenSign (slowValue G c i.val) * |slowValue G c i.val| :=
        congrArg (fun t : ℝ => t * |slowValue G c i.val|) i.property.symm
      _ = _ := eigenSign_mul_abs _
  simp only [modeScale, PiLp.toLp_apply, smul_smul]
  have hvC : (slowValue G c i.val : ℂ) = (s : ℂ) * ((|slowValue G c i.val| : ℝ) : ℂ) := by
    exact_mod_cast hval.symm
  congr 1
  rw [hvC]
  ring

theorem signFrame_normalized (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (s : ℝ)
    (u v : EuclideanSpace ℂ (SignedSlowModes G c s)) :
    ⟪signFrame G hdeg c hc hcouter s u, reversalCLM G (signFrame G hdeg c hc hcouter s v)⟫_ℂ =
      (s : ℂ) * ⟪u, v⟫_ℂ := by
  simp only [signFrame_apply, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, signFrame_basis_pairing]
  simp [mul_ite, mul_comm, mul_left_comm, Finset.mul_sum,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct]

/-- The separate positive/negative frame bound now applies to the actual
graph's constructed modes, without a frame-existence or normalization premise. -/
theorem actual_signFrame_norm_sq_le (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ‖signFrame G hdeg c hc hcouter s‖ ^ 2 ≤ c / (2 * c ^ 2 - 1) := by
  apply single_sign_eigenframe_norm_sq_le G hdeg
    (signFrame G hdeg c hc hcouter s) (fun i => |slowValue G c i.val|) s c hs hc hcouter
  · intro i
    exact i.val.1.property.2.le
  · exact signFrame_eigen G hdeg c hc hcouter s
  · exact signFrame_normalized G hdeg c hc hcouter s

end GirthVerification
