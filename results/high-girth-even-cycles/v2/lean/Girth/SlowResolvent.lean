import Girth.ActualFrame
import Girth.Projector

namespace GirthVerification

open scoped Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem reversalCLM_operator_norm_le_one : ‖reversalCLM G‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [reversalCLM_norm]

noncomputable def modeResolvent (c s : ℝ) (w : ℂ) :
    EuclideanSpace ℂ (SignedSlowModes G c s) →L[ℂ] EuclideanSpace ℂ (SignedSlowModes G c s) :=
  Matrix.toEuclideanCLM (n := SignedSlowModes G c s) (𝕜 := ℂ)
    (Matrix.diagonal (fun i => 1 / (w - (slowValue G c i.val : ℂ))))

theorem modeResolvent_norm_le (c s : ℝ) (w : ℂ) (hw : w.im ≠ 0) :
    ‖modeResolvent G c s w‖ ≤ 1 / |w.im| := by
  have habs : 0 < |w.im| := abs_pos.mpr hw
  rw [modeResolvent, Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 1 / |w.im|)).mpr
  intro i
  rw [norm_div, norm_one]
  apply one_div_le_one_div_of_le habs
  simpa using Complex.abs_im_le_norm (w - (slowValue G c i.val : ℂ))

noncomputable def signedSlowResolvent (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (s : ℝ) (w : ℂ) :
    EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart :=
  (s : ℂ) • (signFrame G hdeg c hc hcouter s).comp
    ((modeResolvent G c s w).comp
      ((signFrame G hdeg c hc hcouter s).adjoint.comp (reversalCLM G)))

theorem signedSlowResolvent_norm_le (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (w : ℂ) (hw : w.im ≠ 0) :
    ‖signedSlowResolvent G hdeg c hc hcouter s w‖ ≤
      (c / (2 * c ^ 2 - 1)) / |w.im| := by
  let F := signFrame G hdeg c hc hcouter s
  let D := modeResolvent G c s w
  let J := reversalCLM G
  have hsNorm : ‖(s : ℂ)‖ = 1 := by rcases hs with rfl | rfl <;> simp
  have hD : ‖D‖ ≤ 1 / |w.im| := modeResolvent_norm_le G c s w hw
  have hJ : ‖J‖ ≤ 1 := reversalCLM_operator_norm_le_one G
  have hF : ‖F‖ ^ 2 ≤ c / (2 * c ^ 2 - 1) := actual_signFrame_norm_sq_le G hdeg c hc hcouter s hs
  change ‖(s : ℂ) • F.comp (D.comp (F.adjoint.comp J))‖ ≤ _
  rw [norm_smul, hsNorm, one_mul]
  calc
    _ ≤ ‖F‖ * ‖D.comp (F.adjoint.comp J)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖F‖ * (‖D‖ * ‖F.adjoint.comp J‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖F‖ * (‖D‖ * (‖F.adjoint‖ * ‖J‖)) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖F‖ * ((1 / |w.im|) * (‖F‖ * 1)) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      gcongr
    _ = ‖F‖ ^ 2 / |w.im| := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hF (abs_nonneg _)

noncomputable def fullSlowResolvent (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) :
    EuclideanSpace ℂ G.Dart →L[ℂ] EuclideanSpace ℂ G.Dart :=
  signedSlowResolvent G hdeg c hc hcouter 1 w + signedSlowResolvent G hdeg c hc hcouter (-1) w

/-- The two sign classes together satisfy display (9), with no loss
depending on graph size or number of modes. Identification with the
explicit projector sum is the next required bridge. -/
theorem fullSlowResolvent_norm_le (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) (hw : w.im ≠ 0) :
    ‖fullSlowResolvent G hdeg c hc hcouter w‖ ≤
      2 * (c / (2 * c ^ 2 - 1)) / |w.im| := by
  calc
    _ ≤ ‖signedSlowResolvent G hdeg c hc hcouter 1 w‖ +
        ‖signedSlowResolvent G hdeg c hc hcouter (-1) w‖ := norm_add_le _ _
    _ ≤ (c / (2 * c ^ 2 - 1)) / |w.im| + (c / (2 * c ^ 2 - 1)) / |w.im| :=
      add_le_add (signedSlowResolvent_norm_le G hdeg c hc hcouter 1 (Or.inl rfl) w hw)
        (signedSlowResolvent_norm_le G hdeg c hc hcouter (-1) (Or.inr rfl) w hw)
    _ = _ := by ring

end GirthVerification
