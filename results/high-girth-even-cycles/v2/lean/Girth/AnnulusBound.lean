import Girth.ReducedComparison

namespace GirthVerification

theorem resolvent_numerator_bound (w : ℂ) (hw : w.im ≠ 0) (hw2 : ‖w‖ ≤ 2) :
    2 * ‖w‖ + 1 / 2 + ‖w‖ / (2 * |w.im|) ≤ 12 / |w.im| := by
  have ha : 0 < |w.im| := abs_pos.mpr hw
  have ha2 : |w.im| ≤ 2 := (Complex.abs_im_le_norm w).trans hw2
  apply (le_div_iff₀ ha).mpr
  have he : (2 * ‖w‖ + 1 / 2 + ‖w‖ / (2 * |w.im|)) * |w.im| =
      (2 * ‖w‖ + 1 / 2) * |w.im| + ‖w‖ / 2 := by field_simp
  rw [he]
  have hp : (2 * ‖w‖ + 1 / 2) * |w.im| ≤ (2 * 2 + 1 / 2) * 2 :=
    mul_le_mul (by linarith) ha2 (abs_nonneg _) (by norm_num)
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A uniform off-axis bound on the annulus used around the power-estimate
contour. The only remaining apparent singularity is `1 / |Im w|`. -/
theorem reducedResolvent_nonreal_annulus_bound (hdeg : MinimumDegreeThree G) (c h : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (hch : c < h)
    (w : ℂ) (hw : w.im ≠ 0) (hwh : h ≤ ‖w‖) (hw2 : ‖w‖ ≤ 2) :
    ‖reducedResolvent G hdeg c hc hcouter w‖ ≤
      (12 / (h ^ 2 - 1 / 2) + 2 * (c / (2 * c ^ 2 - 1))) / |w.im| := by
  have hh : 0 < h := hc.trans hch
  have hh2 : 1 / 2 < h ^ 2 := hcouter.trans ((sq_lt_sq₀ hc.le hh.le).mpr hch)
  have hwc : c < ‖w‖ := hch.trans_le hwh
  have hd : 0 < h ^ 2 - 1 / 2 := by linarith
  have hdw : h ^ 2 - 1 / 2 ≤ ‖w‖ ^ 2 - 1 / 2 := by
    nlinarith [(sq_le_sq₀ hh.le (norm_nonneg w)).mpr hwh]
  have hdwpos : 0 < ‖w‖ ^ 2 - 1 / 2 := hd.trans_le hdw
  have hb := reducedResolvent_nonreal_norm_bound G hdeg c hc hcouter w hw hwc
  have hnum := resolvent_numerator_bound w hw hw2
  have hfirst : (2 * ‖w‖ + 1 / 2 + ‖w‖ / (2 * |w.im|)) / (‖w‖ ^ 2 - 1 / 2) ≤
      (12 / |w.im|) / (h ^ 2 - 1 / 2) := by
    exact (div_le_div_of_nonneg_right hnum hdwpos.le).trans
      (div_le_div_of_nonneg_left (by positivity) hd hdw)
  calc
    _ ≤ (12 / |w.im|) / (h ^ 2 - 1 / 2) + 2 * (c / (2 * c ^ 2 - 1)) / |w.im| :=
      hb.trans (add_le_add hfirst le_rfl)
    _ = _ := by ring

end GirthVerification
