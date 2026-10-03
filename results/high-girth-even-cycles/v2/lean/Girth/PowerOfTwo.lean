import Girth.GraphBounds
import Mathlib.Algebra.Order.Archimedean.Basic

namespace GirthVerification

theorem exists_power_of_two_in_doubling_interval (A : ℝ) (hA : 4 ≤ A) :
    ∃ k : ℕ, 2 ≤ k ∧ A ≤ (2 ^ k : ℕ) ∧ ((2 ^ k : ℕ) : ℝ) ≤ 2 * A := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ A by linarith)
    (show (1 : ℝ) < 2 by norm_num)
  have hnpos : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    subst n
    norm_num at hn'
    linarith
  refine ⟨n + 1, by omega, ?_, ?_⟩
  · exact_mod_cast hn'.le
  · push_cast
    rw [pow_succ]
    linarith

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The corollary follows from the even-length conclusion on this same graph.
This is a proved deduction, not a proof of its still-open antecedent. -/
theorem power_of_two_of_all_even_lengths (hdeg : MinimumDegreeThree G)
    (hn : 0 < Fintype.card V) (hcycles : HasAllEvenLengths G) :
    HasPowerOfTwoCycle G := by
  let A := 4 * Real.log (2 * G.edgeFinset.card : ℝ) / Real.log (20 / 19 : ℝ)
  obtain ⟨k, hk, hklo, hkhi⟩ := exists_power_of_two_in_doubling_interval A
    (left_endpoint_ge_four G hdeg hn)
  refine ⟨k, hk, hcycles (2 ^ k) ?_ ⟨hklo, ?_⟩⟩
  · exact Even.pow_of_ne_zero (by decide : Even (2 : ℕ)) (by omega : k ≠ 0)
  · dsimp [A] at hkhi
    dsimp [InLengthInterval]
    convert hkhi using 1; ring

theorem exact_power_of_two_corollary_of_exact_even_cycle_theorem
    (h : ExactEvenCycleTheorem) : ExactPowerOfTwoCorollary := by
  obtain ⟨n₀, hn₀⟩ := h
  refine ⟨max n₀ 1, ?_⟩
  intro V _ G _ hn hdeg hg
  apply power_of_two_of_all_even_lengths G hdeg
  · omega
  · exact hn₀ V G (le_trans (le_max_left _ _) hn) hdeg hg

end GirthVerification
