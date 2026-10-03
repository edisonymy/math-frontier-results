import Girth.Statement
import Mathlib.Tactic

namespace GirthVerification

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem three_mul_card_le_darts (hdeg : MinimumDegreeThree G) :
    3 * Fintype.card V ≤ 2 * G.edgeFinset.card := by
  calc
    3 * Fintype.card V = ∑ _v : V, 3 := by simp [mul_comm]
    _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum (fun v _ => hdeg v)
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

theorem darts_le_card_mul_pred :
    2 * G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) := by
  calc
    2 * G.edgeFinset.card = ∑ v : V, G.degree v :=
      G.sum_degrees_eq_twice_card_edges.symm
    _ ≤ ∑ _v : V, (Fintype.card V - 1) :=
      Finset.sum_le_sum (fun v _ => Nat.le_sub_one_of_lt (G.degree_lt_card_verts v))
    _ = Fintype.card V * (Fintype.card V - 1) := by simp

theorem darts_lt_card_sq (hn : 0 < Fintype.card V) :
    2 * G.edgeFinset.card < Fintype.card V ^ 2 := by
  apply lt_of_le_of_lt (darts_le_card_mul_pred G)
  rw [pow_two]
  exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hn (by decide)) hn

theorem log_ratio_pos : 0 < Real.log (20 / 19 : ℝ) :=
  Real.log_pos (by norm_num)

theorem left_endpoint_ge_four (hdeg : MinimumDegreeThree G)
    (hn : 0 < Fintype.card V) :
    4 ≤ 4 * Real.log (2 * G.edgeFinset.card : ℝ) / Real.log (20 / 19 : ℝ) := by
  have hN : 3 ≤ 2 * G.edgeFinset.card := by
    have := three_mul_card_le_darts G hdeg
    omega
  have hNr : (3 : ℝ) ≤ (2 * G.edgeFinset.card : ℝ) := by exact_mod_cast hN
  have hlog : Real.log (20 / 19 : ℝ) ≤ Real.log (2 * G.edgeFinset.card : ℝ) :=
    Real.log_le_log (by norm_num) (by linarith)
  apply (le_div_iff₀ log_ratio_pos).mpr
  linarith

end GirthVerification
