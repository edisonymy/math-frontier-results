import Girth.Semisimplicity
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace GirthVerification

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def outerEigenspace (z : ℝ) : Submodule ℂ (G.Dart → ℂ) :=
  (transitionEnd G).genEigenspace (z : ℂ) 1

theorem outerEigenspace_eigen (z : ℝ) (x : outerEigenspace G z) :
    (complexTransition G).mulVec (x : G.Dart → ℂ) = (z : ℂ) • (x : G.Dart → ℂ) :=
  Module.End.mem_genEigenspace_one.mp x.property

noncomputable def signedEigenInnerCore (hdeg : MinimumDegreeThree G)
    (z s : ℝ) (hzouter : 1 / 2 < z ^ 2) (hs : s = 1 ∨ s = -1) (hsz : 0 < s * z) :
    InnerProductSpace.Core ℂ (outerEigenspace G z) where
  inner x y := (s : ℂ) * reversalPairing G x.val y.val
  conj_inner_symm x y := by
    change star ((s : ℂ) * reversalPairing G y.val x.val) = _
    rw [star_mul, reversalPairing_conj_symm]
    simp [mul_comm]
  re_inner_nonneg x := by
    by_cases hx : (x : G.Dart → ℂ) = 0
    · simp [hx, reversalPairing]
    have he := outerEigenspace_eigen G z x
    rcases hs with rfl | rfl
    · have hz : 0 < z := by simpa using hsz
      have hp := positive_outer_reversal_form G hdeg x.val hx z hz hzouter he
      simpa using hp.le
    · have hz : z < 0 := by simpa using hsz
      have hp := negative_outer_reversal_form G hdeg x.val hx z hz hzouter he
      simpa using neg_nonneg.mpr hp.le
  add_left x y w := by
    change (s : ℂ) * reversalPairing G (x.val + y.val) w.val = _
    rw [reversalPairing_add_left, mul_add]
  smul_left x y r := by
    change (s : ℂ) * reversalPairing G (r • x.val) y.val = _
    rw [reversalPairing_smul_left]
    simp only [starRingEnd_apply]
    ring
  definite x hx := by
    apply Subtype.ext
    change (x : G.Dart → ℂ) = 0
    by_contra hne
    have hform := outer_reversal_form_ne_zero G hdeg x.val hne z hzouter
      (outerEigenspace_eigen G z x)
    have hsne : (s : ℂ) ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
    exact hform ((mul_eq_zero.mp hx).resolve_left hsne)

/-- Actual normalized bases exist on every signed outer eigenspace. The
new inner product is constructed from reversal, with positivity proved
from the graph inequality rather than assumed. The conclusion is algebraic. -/
theorem exists_normalized_outer_eigenbasis (hdeg : MinimumDegreeThree G)
    (z s : ℝ) (hzouter : 1 / 2 < z ^ 2) (hs : s = 1 ∨ s = -1) (hsz : 0 < s * z) :
    ∃ b : Module.Basis (Fin (Module.finrank ℂ (outerEigenspace G z))) ℂ (outerEigenspace G z),
      ∀ i j, reversalPairing G (b i).val (b j).val = (s : ℂ) * if i = j then 1 else 0 := by
  classical
  letI C : InnerProductSpace.Core ℂ (outerEigenspace G z) :=
    signedEigenInnerCore G hdeg z s hzouter hs hsz
  letI : NormedAddCommGroup (outerEigenspace G z) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : SeminormedAddCommGroup (outerEigenspace G z) :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ (outerEigenspace G z) :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (outerEigenspace G z))
  let b := stdOrthonormalBasis ℂ (outerEigenspace G z)
  refine ⟨b.toBasis, ?_⟩
  intro i j
  have h := orthonormal_iff_ite.mp b.orthonormal i j
  change (s : ℂ) * reversalPairing G (b i).val (b j).val = if i = j then 1 else 0 at h
  have hss : (s : ℂ) * (s : ℂ) = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hh := congrArg (fun t : ℂ => (s : ℂ) * t) h
  dsimp only at hh
  rw [← mul_assoc, hss, one_mul] at hh
  exact hh

end GirthVerification
