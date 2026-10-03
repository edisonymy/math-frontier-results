import Girth.UniversalThreshold
import Girth.PowerOfTwo

namespace GirthVerification

/-- The exact public graph theorem: an absolute threshold, arbitrary finite
simple graphs, minimum degree three, the fixed girth constant forty, and
every even length in the literal stated interval. -/
theorem exact_even_cycle_theorem : ExactEvenCycleTheorem := by
  classical
  obtain ⟨n₀, hthreshold⟩ := exists_universal_threshold
  refine ⟨n₀, ?_⟩
  intro V instV G instAdj hn₀ hdeg hgir
  obtain ⟨hn, hlog, hg, herr⟩ := hthreshold (Fintype.card V) hn₀
  intro L heven hinterval
  let N : ℕ := 2 * G.edgeFinset.card
  have hnN : Fintype.card V ≤ N := by
    have hh := three_mul_card_le_darts G hdeg
    dsimp [N]
    omega
  have hN : 0 < N := hn.trans_le hnN
  have hNsq : N ≤ Fintype.card V ^ 2 := (darts_lt_card_sq G hn).le
  have hlower : 4 * Real.log (N : ℝ) / Real.log (20 / 19 : ℝ) ≤ (L : ℝ) := by
    simpa [N, Nat.cast_mul, Nat.cast_ofNat] using hinterval.1
  have hupper : (L : ℝ) ≤ 8 * Real.log (N : ℝ) / Real.log (20 / 19 : ℝ) := by
    simpa [N, Nat.cast_mul, Nat.cast_ofNat] using hinterval.2
  have hL : 4 ≤ L := by
    have hh := left_endpoint_ge_four G hdeg hn
    have hr : (4 : ℝ) ≤ (L : ℝ) := hh.trans hinterval.1
    exact_mod_cast hr
  have hLpos : 0 < L := by omega
  have hnum : numericalError (Fintype.card V) N L < 1 :=
    (numericalError_le_universalError (Fintype.card V) N L hn hnN hNsq hLpos hlog hg hlower hupper).trans_lt herr
  have hκ : 0 ≤ collisionDecay G highContour L := by
    simpa [collisionDecay, numericalDecay, N, Nat.cast_mul, Nat.cast_ofNat] using numericalDecay_nonneg N L
  have hκbound : collisionDecay G highContour L ≤ 97 / 100 := by
    simpa [collisionDecay, numericalDecay, N, Nat.cast_mul, Nat.cast_ofNat] using
      numericalDecay_le N L hN hLpos hlower
  have hκone : collisionDecay G highContour L < 1 := by linarith
  have hsucc : L - 1 + 1 = L := by omega
  have hreal : ((L - 1 : ℕ) : ℝ) + 1 = (L : ℝ) := by exact_mod_cast hsucc
  have hcycle := cycle_of_small_error G hdeg highCutoff highContour
    highCutoff_positive highCutoff_outer highCutoff_lt_contour highContour_lt_one hn
    (L - 1) (girthLower (Fintype.card V)) (by omega) (by simpa only [hsucc] using heven)
    (girthLower_le_girth G hgir) (localMassBound (Fintype.card V)) (localMassBound_nonneg _)
    (fun v => highCutoff_local_mass_bound G hdeg hgir hg v)
    (by simpa only [hsucc] using hκ) (by simpa only [hsucc] using hκone)
    (by
      simpa [hsucc, hreal, numericalError, highPowerConstant, numericalDecay, collisionDecay,
        N, Nat.cast_mul, Nat.cast_ofNat] using hnum)
  simpa only [hsucc] using hcycle

theorem exact_power_of_two_corollary : ExactPowerOfTwoCorollary :=
  exact_power_of_two_corollary_of_exact_even_cycle_theorem exact_even_cycle_theorem

end GirthVerification
