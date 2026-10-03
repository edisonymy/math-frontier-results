import Girth.ResidualPower
import Girth.TransitionWalk

namespace GirthVerification

open scoped InnerProductSpace
open WithLp

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def outgoingIndicator (v : V) : EuclideanSpace ℂ G.Dart :=
  toLp 2 (fun e : G.Dart => if e.fst = v then 1 else 0)

theorem outgoingIndicator_apply (v : V) (e : G.Dart) :
    outgoingIndicator G v e = if e.fst = v then 1 else 0 := rfl

theorem outgoingIndicator_norm_sq (v : V) :
    ‖outgoingIndicator G v‖ ^ 2 = (G.degree v : ℝ) := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [outgoingIndicator_apply, apply_ite, norm_one, norm_zero, ite_pow, one_pow, zero_pow
    (by norm_num : (2 : ℕ) ≠ 0)]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [G.dart_fst_fiber_card_eq_degree]

theorem excessDegree_real_pos (hdeg : MinimumDegreeThree G) (v : V) :
    0 < (excessDegree G v : ℝ) := by
  have hh := excessDegree_ge_two G hdeg v
  exact_mod_cast (by omega : 0 < excessDegree G v)

theorem degree_div_excessDegree_le (hdeg : MinimumDegreeThree G) (v : V) :
    (G.degree v : ℝ) / (excessDegree G v : ℝ) ≤ 3 / 2 := by
  have hp := excessDegree_real_pos G hdeg v
  have hd : (3 : ℝ) ≤ G.degree v := by exact_mod_cast hdeg v
  have hq : (excessDegree G v : ℝ) = (G.degree v : ℝ) - 1 := by
    rw [excessDegree, Nat.cast_sub (by have := hdeg v; omega)]
    norm_num
  apply (div_le_iff₀ hp).mpr
  rw [hq]
  linarith

noncomputable def returnMass (t : ℕ) (v : V) : ℝ :=
  (excessDegree G v : ℝ)⁻¹ * ∑ e : G.Dart,
    if e.fst = v then ∑ f : G.Dart,
      if f.snd = v then (transition G ^ (t - 1)) e f else 0 else 0

theorem returnMass_nonneg (t : ℕ) (v : V) : 0 ≤ returnMass G t v := by
  classical
  unfold returnMass
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · apply Finset.sum_nonneg
    intro f _
    split_ifs
    · exact Matrix.pow_apply_nonneg (transition_nonneg G) (t - 1) e f
    · exact le_rfl
  · exact le_rfl

theorem returnMass_eq_zero_below_girth (t : ℕ) (ht : 1 ≤ t) (hg : t < G.girth) (v : V) :
    returnMass G t v = 0 := by
  classical
  unfold returnMass
  suffices ∑ e : G.Dart, (if e.fst = v then ∑ f : G.Dart,
      if f.snd = v then (transition G ^ (t - 1)) e f else 0 else 0) = 0 by rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro e _
  split_ifs with he
  · apply Finset.sum_eq_zero
    intro f _
    split_ifs with hf
    · exact transition_pow_return_eq_zero_below_girth G (t - 1) e f
        (he.trans hf.symm) (by omega)
    · rfl
  · rfl

theorem transitionCLM_pow_matrix (n : ℕ) :
    transitionCLM G ^ n =
      Matrix.toEuclideanCLM (n := G.Dart) (𝕜 := ℂ) (complexLift (transition G ^ n)) := by
  unfold transitionCLM complexTransition complexLift
  rw [Matrix.map_pow, map_pow]
  rfl

/-- The return scalar has exactly the initial `1/q_v` factor of (13).
The closing seam is unrestricted. -/
theorem returnMass_eq_inner (t : ℕ) (v : V) :
    (returnMass G t v : ℂ) = (excessDegree G v : ℂ)⁻¹ *
      ⟪outgoingIndicator G v, (transitionCLM G ^ (t - 1))
        (reversalCLM G (outgoingIndicator G v))⟫_ℂ := by
  classical
  rw [transitionCLM_pow_matrix, EuclideanSpace.inner_eq_star_dotProduct]
  simp [returnMass, dotProduct, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec,
    outgoingIndicator, reversalCLM_apply, complexLift, Complex.ofReal_sum, apply_ite]

end GirthVerification
