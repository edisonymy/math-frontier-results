import Girth.ContourBound
import Girth.ResidualGenerating

namespace GirthVerification

open Metric

set_option synthInstance.maxHeartbeats 200000

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The dimension-independent power estimate (12) for the actual residual
projector. Generalized inner modes need not be diagonalizable. -/
theorem residual_power_norm_bound (hdeg : MinimumDegreeThree G) (c b : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (hcb : c < b) (hb : b < 1) (n : ℕ) :
    ‖transitionCLM G ^ n * residualProjectorCLM G hdeg c hc hcouter‖ ≤
      (2 * b * remainderConstant c b / cutoffRadius c b) * b ^ n := by
  have hbpos := hc.trans hcb
  have hr : 0 < b⁻¹ := inv_pos.mpr hbpos
  have hprod : ∀ z ∈ closedBall (0 : ℂ) b⁻¹, c * ‖z‖ < 1 := by
    intro z hz
    have hn : ‖z‖ ≤ b⁻¹ := mem_closedBall_zero_iff.mp hz
    calc
      c * ‖z‖ ≤ c * b⁻¹ := mul_le_mul_of_nonneg_left hn hc.le
      _ < 1 := by rw [← div_eq_mul_inv]; exact (div_lt_one hbpos).mpr hcb
  have hd : DifferentiableOn ℂ (residualGenerating G hdeg c hc hcouter)
      (closedBall 0 b⁻¹) := by
    intro z hz
    exact (residualGenerating_analyticAt G hdeg c hc hcouter z (hprod z hz)).differentiableAt.differentiableWithinAt
  have hbound : ∀ z ∈ sphere (0 : ℂ) b⁻¹,
      ‖residualGenerating G hdeg c hc hcouter z‖ ≤
        2 * b * remainderConstant c b / cutoffRadius c b := by
    intro z hz
    have hn : ‖z‖ = b⁻¹ := mem_sphere_zero_iff_norm.mp hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hn ▸ hr)
    have hw : ‖z⁻¹‖ = b := by simp [norm_inv, hn]
    rw [residualGenerating_eq_resolvent G hdeg c hc hcouter z hz0
      (hprod z (sphere_subset_closedBall hz)), norm_smul, hw]
    calc
      _ ≤ b * (2 * remainderConstant c b / cutoffRadius c b) :=
        mul_le_mul_of_nonneg_left
          (reducedResolvent_circle_norm_bound G hdeg c b hc hcouter hcb hb z⁻¹ hw) hbpos.le
      _ = _ := by ring
  have h := inverse_one_sub_power_bound
    (residualRestrictedCLM G hdeg c hc hcouter) (residualSandwich G hdeg c hc hcouter)
    b⁻¹ (2 * b * remainderConstant c b / cutoffRadius c b) hr hd hbound n
  rw [residualSandwich_pow, inv_inv] at h
  exact h

end GirthVerification
