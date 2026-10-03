import Girth.OuterBasis
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

namespace GirthVerification

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem hasEigenvalue_normSq_le_one (hdeg : MinimumDegreeThree G) (z : ℂ)
    (hz : (transitionEnd G).HasEigenvalue z) : Complex.normSq z ≤ 1 := by
  obtain ⟨x, hx⟩ := hz.exists_hasEigenvector
  exact eigenvalue_normSq_le_one G hdeg x hx.2 z hx.apply_eq_smul

theorem outer_eigenvalue_im_zero (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (z : ℂ)
    (hz : (transitionEnd G).HasEigenvalue z) (hzouter : c < ‖z‖) : z.im = 0 := by
  by_contra him
  obtain ⟨x, hx⟩ := hz.exists_hasEigenvector
  have hb := nonreal_eigenvalue_normSq_le_half G hdeg x hx.2 z him hx.apply_eq_smul
  have hsq : c ^ 2 < ‖z‖ ^ 2 := (sq_lt_sq₀ hc.le (norm_nonneg z)).mpr hzouter
  rw [Complex.normSq_eq_norm_sq] at hb
  linarith

def outerRealEigenvalues (c : ℝ) : Type :=
  {z : ℝ // (transitionEnd G).HasEigenvalue (z : ℂ) ∧ c < |z|}

noncomputable instance (c : ℝ) : Fintype (outerRealEigenvalues G c) := by
  classical
  let f : outerRealEigenvalues G c → (transitionEnd G).Eigenvalues :=
    fun z => ⟨(z.val : ℂ), z.property.1⟩
  apply Fintype.ofInjective f
  intro a b h
  apply Subtype.ext
  apply Complex.ofReal_injective
  exact congrArg Subtype.val h

/-- The finite real index includes exactly the eigenvalues removed by a
cutoff above the inner disc; no nonreal outer eigenvalue is omitted. -/
theorem outer_eigenvalue_in_real_index (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (z : ℂ)
    (hz : (transitionEnd G).HasEigenvalue z) (hzouter : c < ‖z‖) :
    ∃ r : outerRealEigenvalues G c, (r.val : ℂ) = z := by
  have him := outer_eigenvalue_im_zero G hdeg c hc hcouter z hz hzouter
  have heq : (z.re : ℂ) = z := Complex.ext rfl (by simpa using him.symm)
  refine ⟨⟨z.re, ?_, ?_⟩, heq⟩
  · rwa [heq]
  · rw [← heq, Complex.norm_real] at hzouter
    exact hzouter

noncomputable def eigenSign (z : ℝ) : ℝ := if 0 ≤ z then 1 else -1

theorem eigenSign_cases (z : ℝ) : eigenSign z = 1 ∨ eigenSign z = -1 := by
  classical
  unfold eigenSign
  split_ifs <;> simp

theorem eigenSign_mul_pos (z : ℝ) (hz : z ≠ 0) : 0 < eigenSign z * z := by
  classical
  by_cases h : 0 ≤ z
  · simp only [eigenSign, if_pos h, one_mul]
    exact lt_of_le_of_ne h (Ne.symm hz)
  · simp only [eigenSign, if_neg h, neg_one_mul]
    exact neg_pos.mpr (lt_of_not_ge h)

theorem outer_real_sq_gt_half (c : ℝ) (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2)
    (z : outerRealEigenvalues G c) : 1 / 2 < z.val ^ 2 := by
  have hsq := (sq_lt_sq₀ hc.le (abs_nonneg z.val)).mpr z.property.2
  rw [sq_abs] at hsq
  exact hcouter.trans hsq

noncomputable def normalizedOuterBasis (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (z : outerRealEigenvalues G c) :
    Module.Basis (Fin (Module.finrank ℂ (outerEigenspace G z.val))) ℂ (outerEigenspace G z.val) :=
  (exists_normalized_outer_eigenbasis G hdeg z.val (eigenSign z.val)
    (outer_real_sq_gt_half G c hc hcouter z) (eigenSign_cases z.val)
    (eigenSign_mul_pos z.val (by have := z.property.2; rintro h; simp [h] at this; linarith))).choose

theorem normalizedOuterBasis_pairing (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (z : outerRealEigenvalues G c) (i j) :
    reversalPairing G (normalizedOuterBasis G hdeg c hc hcouter z i).val
      (normalizedOuterBasis G hdeg c hc hcouter z j).val =
        (eigenSign z.val : ℂ) * if i = j then 1 else 0 := by
  exact (exists_normalized_outer_eigenbasis G hdeg z.val (eigenSign z.val)
    (outer_real_sq_gt_half G c hc hcouter z) (eigenSign_cases z.val)
    (eigenSign_mul_pos z.val (by have := z.property.2; rintro h; simp [h] at this; linarith))).choose_spec i j

theorem transitionEnd_hasEigenvalue_one (hdeg : MinimumDegreeThree G)
    (hn : 0 < Fintype.card V) : (transitionEnd G).HasEigenvalue 1 := by
  have hN : 0 < Fintype.card G.Dart := by
    rw [G.dart_card_eq_twice_card_edges]
    have h := three_mul_card_le_darts G hdeg
    omega
  obtain ⟨e⟩ : Nonempty G.Dart := Fintype.card_pos_iff.mp hN
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := fun _ : G.Dart => (1 : ℂ))
  rw [Module.End.hasEigenvector_iff]
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    change (complexTransition G).mulVec (fun _ => (1 : ℂ)) = 1 • (fun _ => (1 : ℂ))
    ext f
    simp only [Matrix.mulVec, dotProduct, mul_one, complexTransition, Matrix.map_apply,
      ← Complex.ofReal_sum, transition_row_sum G hdeg, Complex.ofReal_one, one_smul]
  · intro h
    have h' := congrFun h e
    norm_num at h'

end GirthVerification
