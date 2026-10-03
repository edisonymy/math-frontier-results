import Girth.JordanObstruction
import Mathlib.LinearAlgebra.Eigenspace.Basic

namespace GirthVerification

theorem pow_kernel_mem_implies_kernel_mem {K M : Type*} [Field K]
    [AddCommGroup M] [Module K M] (f : Module.End K M)
    (h : ∀ x, f (f x) = 0 → f x = 0) (n : ℕ) (x : M) (hx : (f ^ n) x = 0) :
    f x = 0 := by
  induction n generalizing x with
  | zero =>
    have hx' : x = 0 := by simpa using hx
    simp [hx']
  | succ n ih =>
    have hx' : (f ^ n) (f x) = 0 := by simpa [pow_succ, Module.End.mul_apply] using hx
    exact h x (ih (f x) hx')

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def transitionEnd : Module.End ℂ (G.Dart → ℂ) :=
  Matrix.toLin' (complexTransition G)

theorem outer_shift_no_kernel_pair (hdeg : MinimumDegreeThree G) (z : ℝ)
    (hz : 1 / 2 < z ^ 2) (y : G.Dart → ℂ) :
    (transitionEnd G - (z : ℂ) • 1) ((transitionEnd G - (z : ℂ) • 1) y) = 0 →
      (transitionEnd G - (z : ℂ) • 1) y = 0 := by
  intro hy
  let x := (transitionEnd G - (z : ℂ) • 1) y
  by_contra hx
  have hPx : (complexTransition G).mulVec x = (z : ℂ) • x := by
    change (complexTransition G).mulVec x - (z : ℂ) • x = 0 at hy
    exact sub_eq_zero.mp hy
  apply no_outer_jordan_pair G hdeg x hx z hz hPx
  refine ⟨y, ?_⟩
  change (complexTransition G).mulVec y = (z : ℂ) • y +
    ((complexTransition G).mulVec y - (z : ℂ) • y)
  abel

/-- All generalized eigenspaces of a real outer eigenvalue collapse to the
ordinary eigenspace. No diagonalizability of the remaining spectrum follows. -/
theorem outer_genEigenspace_eq_eigenspace (hdeg : MinimumDegreeThree G) (z : ℝ)
    (hz : 1 / 2 < z ^ 2) :
    (transitionEnd G).genEigenspace (z : ℂ) ⊤ =
      (transitionEnd G).genEigenspace (z : ℂ) 1 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := Module.End.mem_genEigenspace_top.mp hx
    rw [LinearMap.mem_ker] at hn
    rw [Module.End.genEigenspace_one, LinearMap.mem_ker]
    exact pow_kernel_mem_implies_kernel_mem _ (outer_shift_no_kernel_pair G hdeg z hz) n x hn
  · exact ((transitionEnd G).genEigenspace (z : ℂ)).monotone le_top

theorem reversalPairing_shift_right (x y : G.Dart → ℂ) (z : ℝ) (w : ℂ)
    (hPx : (complexTransition G).mulVec x = (z : ℂ) • x) :
    reversalPairing G x ((transitionEnd G - w • 1) y) =
      ((z : ℂ) - w) * reversalPairing G x y := by
  change reversalPairing G x ((complexTransition G).mulVec y - w • y) = _
  rw [sub_eq_add_neg, ← neg_one_smul ℂ (w • y), reversalPairing_add_right,
    reversalPairing_smul_right, reversalPairing_smul_right,
    reversalPairing_eigen_left G x z hPx]
  ring

/-- A real left eigenvector annihilates every generalized eigenspace at a
different eigenvalue, including nonreal eigenvalues and Jordan blocks. -/
theorem eigenvector_generalized_reversal_orthogonal
    (x : G.Dart → ℂ) (z : ℝ) (w : ℂ) (hzw : (z : ℂ) ≠ w)
    (hPx : (complexTransition G).mulVec x = (z : ℂ) • x)
    (n : ℕ) (y : G.Dart → ℂ)
    (hy : ((transitionEnd G - w • 1) ^ n) y = 0) : reversalPairing G x y = 0 := by
  induction n generalizing y with
  | zero =>
    have hy' : y = 0 := by simpa using hy
    simp [hy', reversalPairing]
  | succ n ih =>
    have hy' : ((transitionEnd G - w • 1) ^ n) ((transitionEnd G - w • 1) y) = 0 := by
      simpa [pow_succ, Module.End.mul_apply] using hy
    have hp := ih _ hy'
    rw [reversalPairing_shift_right G x y z w hPx] at hp
    exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hzw)

end GirthVerification
