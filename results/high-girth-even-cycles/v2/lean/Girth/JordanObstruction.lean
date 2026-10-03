import Girth.OuterSpectrum

namespace GirthVerification

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def reversalPairing (x y : G.Dart → ℂ) : ℂ :=
  ∑ e, star (x e) * (complexLift (reversal G)).mulVec y e

theorem reversalPairing_conj_symm (x y : G.Dart → ℂ) :
    star (reversalPairing G y x) = reversalPairing G x y := by
  change star (star y ⬝ᵥ (complexLift (reversal G)).mulVec x) =
    star x ⬝ᵥ (complexLift (reversal G)).mulVec y
  rw [← Matrix.star_dotProduct, Matrix.star_mulVec, (complexLift_isHermitian _
    (reversal_isHermitian G)).eq, ← Matrix.dotProduct_mulVec]

theorem reversalPairing_add_left (x y w : G.Dart → ℂ) :
    reversalPairing G (x + y) w = reversalPairing G x w + reversalPairing G y w := by
  simp [reversalPairing, star_add, add_mul, Finset.sum_add_distrib]

theorem reversalPairing_smul_left (x y : G.Dart → ℂ) (z : ℂ) :
    reversalPairing G (z • x) y = star z * reversalPairing G x y := by
  simp [reversalPairing, Pi.smul_apply, star_mul, smul_eq_mul, mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem reversalPairing_eigen_left (x : G.Dart → ℂ) (z : ℝ)
    (hPx : (complexTransition G).mulVec x = (z : ℂ) • x) (y : G.Dart → ℂ) :
    reversalPairing G x ((complexTransition G).mulVec y) =
      (z : ℂ) * reversalPairing G x y := by
  calc
    _ = ∑ e, star (x e) * (complexLift (reversal G * transition G)).mulVec y e := by
      rw [complexLift_mul, ← Matrix.mulVec_mulVec]
      rfl
    _ = ∑ e, star ((complexLift (reversal G * transition G)).mulVec x e) * y e :=
      hermitian_pairing_transfer _ (reversal_mul_transition_isHermitian G) x y
    _ = (z : ℂ) * ∑ e, star ((complexLift (reversal G)).mulVec x e) * y e := by
      rw [complexLift_mul, ← Matrix.mulVec_mulVec]
      change (∑ e, star ((complexLift (reversal G)).mulVec
        ((complexTransition G).mulVec x) e) * y e) = _
      rw [hPx]
      simp [Matrix.mulVec_smul, Pi.smul_apply, mul_assoc, Finset.mul_sum]
    _ = (z : ℂ) * reversalPairing G x y := by
      rw [← hermitian_pairing_transfer _ (reversal_isHermitian G) x y]
      rfl

theorem reversalPairing_add_right (x y w : G.Dart → ℂ) :
    reversalPairing G x (y + w) = reversalPairing G x y + reversalPairing G x w := by
  simp [reversalPairing, Matrix.mulVec_add, mul_add, Finset.sum_add_distrib]

theorem reversalPairing_smul_right (x y : G.Dart → ℂ) (z : ℂ) :
    reversalPairing G x (z • y) = z * reversalPairing G x y := by
  simp [reversalPairing, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem distinct_real_eigenvectors_reversal_orthogonal
    (x y : G.Dart → ℂ) (z w : ℝ) (hzw : z ≠ w)
    (hPx : (complexTransition G).mulVec x = (z : ℂ) • x)
    (hPy : (complexTransition G).mulVec y = (w : ℂ) • y) :
    reversalPairing G x y = 0 := by
  have h := reversalPairing_eigen_left G x z hPx y
  rw [hPy, reversalPairing_smul_right] at h
  have hm : ((z : ℂ) - (w : ℂ)) * reversalPairing G x y = 0 := by linear_combination -h
  have hne : (z : ℂ) - (w : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (fun he => hzw (Complex.ofReal_injective he))
  exact (mul_eq_zero.mp hm).resolve_left hne

/-- No nonzero outer eigenvector can be the terminal vector of a length-two
Jordan chain. This is the substantive semisimplicity obstruction in §3. -/
theorem no_outer_jordan_pair (hdeg : MinimumDegreeThree G)
    (x : G.Dart → ℂ) (hx : x ≠ 0) (z : ℝ) (hzouter : 1 / 2 < z ^ 2)
    (hPx : (complexTransition G).mulVec x = (z : ℂ) • x) :
    ¬ ∃ y : G.Dart → ℂ, (complexTransition G).mulVec y = (z : ℂ) • y + x := by
  rintro ⟨y, hy⟩
  have h := reversalPairing_eigen_left G x z hPx y
  rw [hy, reversalPairing_add_right, reversalPairing_smul_right] at h
  have hz : reversalPairing G x x = 0 := by linear_combination h
  exact outer_reversal_form_ne_zero G hdeg x hx z hzouter hPx hz

end GirthVerification
