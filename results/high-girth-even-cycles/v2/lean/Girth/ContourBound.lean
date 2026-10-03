import Girth.AnnulusBound
import Girth.OperatorRealAxisBound

namespace GirthVerification

open Metric

noncomputable def cutoffRadius (c b : ℝ) : ℝ := (b - c) / 2
noncomputable def cutoffMidpoint (c b : ℝ) : ℝ := (b + c) / 2
noncomputable def remainderConstant (c b : ℝ) : ℝ :=
  12 / (cutoffMidpoint c b ^ 2 - 1 / 2) + 2 * (c / (2 * c ^ 2 - 1))

theorem cutoffRadius_pos (c b : ℝ) (hcb : c < b) : 0 < cutoffRadius c b := by
  unfold cutoffRadius
  linarith

theorem cutoff_disc_in_annulus (c b : ℝ) (hc : 0 < c) (hcb : c < b) (hb : b < 1)
    (z w : ℂ) (hz : ‖z‖ = b) (hw : w ∈ closedBall z (cutoffRadius c b)) :
    cutoffMidpoint c b ≤ ‖w‖ ∧ ‖w‖ < 2 := by
  have hdist : ‖w - z‖ ≤ cutoffRadius c b := by simpa [mem_closedBall, dist_eq_norm] using hw
  have hdist' : ‖z - w‖ ≤ cutoffRadius c b := by simpa [norm_sub_rev] using hdist
  have hlo : b ≤ ‖w‖ + cutoffRadius c b := by
    calc
      b = ‖w + (z - w)‖ := by rw [← hz]; congr 1; abel
      _ ≤ ‖w‖ + ‖z - w‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl hdist'
  have hhi : ‖w‖ ≤ b + cutoffRadius c b := by
    calc
      ‖w‖ = ‖z + (w - z)‖ := by congr 1; abel
      _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
      _ ≤ _ := by rw [hz]; exact add_le_add le_rfl hdist
  unfold cutoffRadius at hlo hhi
  unfold cutoffMidpoint
  constructor <;> linarith

theorem remainderConstant_gt_two (c b : ℝ) (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2)
    (hcb : c < b) (hb : b < 1) : 2 < remainderConstant c b := by
  have hmid : c < cutoffMidpoint c b := by unfold cutoffMidpoint; linarith
  have hmpos : 0 < cutoffMidpoint c b := hc.trans hmid
  have hmone : cutoffMidpoint c b < 1 := by unfold cutoffMidpoint; linarith
  have hmsq : 1 / 2 < cutoffMidpoint c b ^ 2 :=
    hcouter.trans ((sq_lt_sq₀ hc.le hmpos.le).mpr hmid)
  have hd : 0 < cutoffMidpoint c b ^ 2 - 1 / 2 := by linarith
  have hcsq : 0 < 2 * c ^ 2 - 1 := by linarith
  have hfirst : 2 < 12 / (cutoffMidpoint c b ^ 2 - 1 / 2) := by
    apply (lt_div_iff₀ hd).mpr
    have hs := (sq_lt_sq₀ hmpos.le (by norm_num : (0 : ℝ) ≤ 1)).mpr hmone
    nlinarith
  unfold remainderConstant
  have hlast : 0 ≤ 2 * (c / (2 * c ^ 2 - 1)) := by positivity
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Uniform reduced-resolvent bound on the whole contour, including its
real points. This is the analytic estimate preceding display (12). -/
theorem reducedResolvent_circle_norm_bound (hdeg : MinimumDegreeThree G) (c b : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (hcb : c < b) (hb : b < 1)
    (z : ℂ) (hz : ‖z‖ = b) :
    ‖reducedResolvent G hdeg c hc hcouter z‖ ≤ 2 * remainderConstant c b / cutoffRadius c b := by
  have hη := cutoffRadius_pos c b hcb
  have hC := remainderConstant_gt_two c b hc hcouter hcb hb
  have hmid : c < cutoffMidpoint c b := by unfold cutoffMidpoint; linarith
  apply analytic_operator_norm_bound_from_imaginary _ z (cutoffRadius c b) (remainderConstant c b)
    hη (by linarith)
  · intro w hw
    have hlo := (cutoff_disc_in_annulus c b hc hcb hb z w hz hw).1
    exact reducedResolvent_analyticOnNhd G hdeg c hc hcouter w (hmid.trans_le hlo)
  · intro w hw
    have hhi := (cutoff_disc_in_annulus c b hc hcb hb z w hz (sphere_subset_closedBall hw)).2
    exact (Complex.abs_im_le_norm w).trans (by linarith)
  · intro w hw him
    have hAnn := cutoff_disc_in_annulus c b hc hcb hb z w hz (sphere_subset_closedBall hw)
    exact reducedResolvent_nonreal_annulus_bound G hdeg c (cutoffMidpoint c b) hc hcouter hmid
      w him hAnn.1 hAnn.2.le

end GirthVerification
