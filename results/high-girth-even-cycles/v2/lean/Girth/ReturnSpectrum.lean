import Girth.ReturnAlgebra

namespace GirthVerification

open scoped InnerProductSpace
open WithLp

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def vertexModeWeight (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (v : V) (i : SlowModes G c) : ℝ :=
  ‖⟪outgoingIndicator G v, toLp 2 (slowVector G hdeg c hc hcouter i)⟫_ℂ‖ ^ 2 /
    ((excessDegree G v : ℝ) * |slowValue G c i|)

theorem vertexModeWeight_nonneg (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (v : V) (i : SlowModes G c) :
    0 ≤ vertexModeWeight G hdeg c hc hcouter v i := by
  unfold vertexModeWeight
  positivity

theorem slowProjectorCLM_apply (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (x : EuclideanSpace ℂ G.Dart) :
    slowProjectorCLM G hdeg c hc hcouter x =
      ∑ i, slowCoordinate G hdeg c hc hcouter i (ofLp x) •
        toLp 2 (slowVector G hdeg c hc hcouter i) := by
  ext e
  simp [slowProjectorCLM, euclideanEndLift, slowProjector_apply]

theorem transitionCLM_pow_slowVector (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (i : SlowModes G c) (n : ℕ) :
    (transitionCLM G ^ n) (toLp 2 (slowVector G hdeg c hc hcouter i)) =
      (slowValue G c i : ℂ) ^ n • toLp 2 (slowVector G hdeg c hc hcouter i) := by
  have he : transitionCLM G (toLp 2 (slowVector G hdeg c hc hcouter i)) =
      (slowValue G c i : ℂ) • toLp 2 (slowVector G hdeg c hc hcouter i) := by
    ext e
    exact congrFun (slowVector_eigen G hdeg c hc hcouter i) e
  induction n with
  | zero => simp [ContinuousLinearMap.one_def]
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, he, smul_smul, pow_succ]

theorem slowCoordinate_reversalCLM (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (i : SlowModes G c)
    (x : EuclideanSpace ℂ G.Dart) :
    slowCoordinate G hdeg c hc hcouter i (ofLp (reversalCLM G x)) =
      (eigenSign (slowValue G c i) : ℂ) *
        ⟪toLp 2 (slowVector G hdeg c hc hcouter i), x⟫_ℂ := by
  rw [slowCoordinate_apply, ← euclidean_reversalPairing_eq]
  change (eigenSign (slowValue G c i) : ℂ) *
    ⟪toLp 2 (slowVector G hdeg c hc hcouter i), reversalCLM G (reversalCLM G x)⟫_ℂ = _
  rw [reversalCLM_sq_apply]

theorem slowReturn_inner_formula (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (v : V) (n : ℕ) :
    ⟪outgoingIndicator G v, (transitionCLM G ^ n)
      (slowProjectorCLM G hdeg c hc hcouter (reversalCLM G (outgoingIndicator G v)))⟫_ℂ =
      ∑ i : SlowModes G c, (eigenSign (slowValue G c i) : ℂ) * (slowValue G c i : ℂ) ^ n *
        (‖⟪outgoingIndicator G v, toLp 2 (slowVector G hdeg c hc hcouter i)⟫_ℂ‖ ^ 2 : ℝ) := by
  classical
  rw [slowProjectorCLM_apply, map_sum, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, transitionCLM_pow_slowVector, slowCoordinate_reversalCLM,
    smul_smul, inner_smul_right]
  have hp : ⟪toLp 2 (slowVector G hdeg c hc hcouter i), outgoingIndicator G v⟫_ℂ *
      ⟪outgoingIndicator G v, toLp 2 (slowVector G hdeg c hc hcouter i)⟫_ℂ =
      (‖⟪outgoingIndicator G v, toLp 2 (slowVector G hdeg c hc hcouter i)⟫_ℂ‖ ^ 2 : ℝ) := by
    rw [← inner_conj_symm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  calc
    _ = (eigenSign (slowValue G c i) : ℂ) * (slowValue G c i : ℂ) ^ n *
        (⟪toLp 2 (slowVector G hdeg c hc hcouter i), outgoingIndicator G v⟫_ℂ *
          ⟪outgoingIndicator G v, toLp 2 (slowVector G hdeg c hc hcouter i)⟫_ℂ) := by ring
    _ = _ := by rw [hp]

theorem eigenSign_power_weight (z : ℝ) (n : ℕ) :
    eigenSign z * z ^ n * |z| = eigenSign z ^ (n + 1) * |z| ^ (n + 1) := by
  nth_rw 2 [← eigenSign_mul_abs z]
  rw [mul_pow, pow_succ, pow_succ]
  ring

theorem slowReturn_weight_formula (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (v : V) (t : ℕ) (ht : 1 ≤ t) :
    (excessDegree G v : ℂ)⁻¹ *
      ⟪outgoingIndicator G v, (transitionCLM G ^ (t - 1))
        (slowProjectorCLM G hdeg c hc hcouter (reversalCLM G (outgoingIndicator G v)))⟫_ℂ =
      (∑ i : SlowModes G c, eigenSign (slowValue G c i) ^ t * |slowValue G c i| ^ t *
        vertexModeWeight G hdeg c hc hcouter v i : ℝ) := by
  rw [slowReturn_inner_formula, Finset.mul_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hq := ne_of_gt (excessDegree_real_pos G hdeg v)
  have hz : |slowValue G c i| ≠ 0 := ne_of_gt (hc.trans i.1.property.2)
  have he := eigenSign_power_weight (slowValue G c i) (t - 1)
  have ht' : t - 1 + 1 = t := by omega
  rw [ht'] at he
  simp only [vertexModeWeight, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_natCast]
  have heC := congrArg Complex.ofReal he
  push_cast at heC
  have hqC : (excessDegree G v : ℂ) ≠ 0 := by exact_mod_cast hq
  have hzC : Complex.ofReal |slowValue G c i| ≠ 0 := by exact_mod_cast hz
  field_simp [hqC, hzC]
  linear_combination (Complex.ofReal
    ‖⟪outgoingIndicator G v, toLp 2 (slowVector G hdeg c hc hcouter i)⟫_ℂ‖) ^ 2 * heC

end GirthVerification
