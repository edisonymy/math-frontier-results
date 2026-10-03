import Girth.ReturnSpectrum

namespace GirthVerification

open scoped InnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def returnConstant (c b : ℝ) : ℝ :=
  3 * remainderConstant c b / cutoffRadius c b

noncomputable def signedReturnMain (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (t : ℕ) (v : V) : ℝ :=
  ∑ i : SlowModes G c, eigenSign (slowValue G c i) ^ t * |slowValue G c i| ^ t *
    vertexModeWeight G hdeg c hc hcouter v i

noncomputable def returnError (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (t : ℕ) (v : V) : ℝ :=
  ((excessDegree G v : ℂ)⁻¹ *
    ⟪outgoingIndicator G v, (transitionCLM G ^ (t - 1) * residualProjectorCLM G hdeg c hc hcouter)
      (reversalCLM G (outgoingIndicator G v))⟫_ℂ).re

/-- The actual return expansion (14), with its signed normalized modes. -/
theorem returnMass_eq_main_add_error (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (t : ℕ) (ht : 1 ≤ t) (v : V) :
    returnMass G t v = signedReturnMain G hdeg c hc hcouter t v +
      returnError G hdeg c hc hcouter t v := by
  have hsplit : (transitionCLM G ^ (t - 1)) (reversalCLM G (outgoingIndicator G v)) =
      (transitionCLM G ^ (t - 1))
        (slowProjectorCLM G hdeg c hc hcouter (reversalCLM G (outgoingIndicator G v))) +
      (transitionCLM G ^ (t - 1) * residualProjectorCLM G hdeg c hc hcouter)
        (reversalCLM G (outgoingIndicator G v)) := by
    rw [residualProjectorCLM_eq_sub]
    simp [ContinuousLinearMap.mul_apply, map_sub]
  have hh := returnMass_eq_inner G t v
  rw [hsplit, inner_add_right, mul_add,
    slowReturn_weight_formula G hdeg c hc hcouter v t ht] at hh
  exact congrArg Complex.re hh

theorem returnError_abs_bound (hdeg : MinimumDegreeThree G) (c b : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (hcb : c < b) (hb : b < 1)
    (t : ℕ) (ht : 1 ≤ t) (v : V) :
    |returnError G hdeg c hc hcouter t v| ≤ returnConstant c b * b ^ t := by
  have hqpos := excessDegree_real_pos G hdeg v
  have hη := cutoffRadius_pos c b hcb
  have hC := remainderConstant_gt_two c b hc hcouter hcb hb
  have hbpos := hc.trans hcb
  let T := transitionCLM G ^ (t - 1) * residualProjectorCLM G hdeg c hc hcouter
  have hT := residual_power_norm_bound G hdeg c b hc hcouter hcb hb (t - 1)
  have hbase : |returnError G hdeg c hc hcouter t v| ≤
      ((G.degree v : ℝ) / (excessDegree G v : ℝ)) * ‖T‖ := by
    unfold returnError
    calc
      _ ≤ ‖(excessDegree G v : ℂ)⁻¹ *
          ⟪outgoingIndicator G v, T (reversalCLM G (outgoingIndicator G v))⟫_ℂ‖ :=
        Complex.abs_re_le_norm _
      _ = (excessDegree G v : ℝ)⁻¹ *
          ‖⟪outgoingIndicator G v, T (reversalCLM G (outgoingIndicator G v))⟫_ℂ‖ := by
        rw [norm_mul, norm_inv]
        simp
      _ ≤ (excessDegree G v : ℝ)⁻¹ *
          (‖outgoingIndicator G v‖ * ‖T (reversalCLM G (outgoingIndicator G v))‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by positivity)
      _ ≤ (excessDegree G v : ℝ)⁻¹ *
          (‖outgoingIndicator G v‖ * (‖T‖ * ‖reversalCLM G (outgoingIndicator G v)‖)) := by
        gcongr
        exact T.le_opNorm _
      _ = ((G.degree v : ℝ) / (excessDegree G v : ℝ)) * ‖T‖ := by
        rw [reversalCLM_norm]
        have hd := outgoingIndicator_norm_sq G v
        rw [← hd]
        ring
  calc
    _ ≤ ((G.degree v : ℝ) / (excessDegree G v : ℝ)) * ‖T‖ := hbase
    _ ≤ (3 / 2 : ℝ) * ‖T‖ := mul_le_mul_of_nonneg_right
      (degree_div_excessDegree_le G hdeg v) (norm_nonneg _)
    _ ≤ (3 / 2 : ℝ) * ((2 * b * remainderConstant c b / cutoffRadius c b) * b ^ (t - 1)) :=
      mul_le_mul_of_nonneg_left hT (by norm_num)
    _ = returnConstant c b * b ^ t := by
      unfold returnConstant
      have ht' : t = (t - 1) + 1 := by omega
      conv_rhs => rw [ht', pow_succ]
      ring

end GirthVerification
