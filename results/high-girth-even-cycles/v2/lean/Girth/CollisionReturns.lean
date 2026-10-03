import Girth.MatrixMarker
import Girth.FiniteChain
import Girth.ReturnAlgebra

namespace GirthVerification

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def returnRow (t : ℕ) (v : V) (e : G.Dart) : ℝ :=
  ∑ f : G.Dart, if f.snd = v then (transition G ^ (t - 1)) e f else 0

theorem returnRow_nonneg (t : ℕ) (v : V) (e : G.Dart) : 0 ≤ returnRow G t v e := by
  classical
  exact Finset.sum_nonneg (fun f _ => by
    split_ifs
    · exact Matrix.pow_apply_nonneg (transition_nonneg G) (t - 1) e f
    · exact le_rfl)

theorem transition_le_closing_weight (e f : G.Dart) :
    transition G e f ≤ if e.snd = f.fst then (excessDegree G f.fst : ℝ)⁻¹ else 0 := by
  classical
  by_cases hnb : NonBacktracking G e f
  · simp [transition, hnb, hnb.1, one_div]
  · simp [transition, hnb]
    split_ifs <;> positivity

theorem transition_pow_le_returnRow (t : ℕ) (ht : 1 ≤ t) (e f : G.Dart) :
    (transition G ^ t) e f ≤ (excessDegree G f.fst : ℝ)⁻¹ * returnRow G t f.fst e := by
  classical
  have htn : t = t - 1 + 1 := by omega
  conv_lhs => rw [htn, pow_succ, Matrix.mul_apply]
  unfold returnRow
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g _
  have h := mul_le_mul_of_nonneg_left (transition_le_closing_weight G g f)
    (Matrix.pow_apply_nonneg (transition_nonneg G) (t - 1) e g)
  exact h.trans_eq (by split_ifs <;> ring)

theorem sum_same_fst_eq_vertex_sum (F : G.Dart → G.Dart → ℝ) :
    (∑ e : G.Dart, ∑ f : G.Dart, if e.fst = f.fst then F e f else 0) =
      ∑ v : V, ∑ e : G.Dart, if e.fst = v then
        ∑ f : G.Dart, if f.fst = v then F e f else 0 else 0 := by
  classical
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [eq_comm]

theorem sum_returnRows_eq_product (t s : ℕ) (v : V) :
    (∑ e : G.Dart, if e.fst = v then ∑ f : G.Dart, if f.fst = v then
      ((excessDegree G v : ℝ)⁻¹ * returnRow G t v e) *
        ((excessDegree G v : ℝ)⁻¹ * returnRow G s v f) else 0 else 0) =
      returnMass G t v * returnMass G s v := by
  classical
  change _ = ((excessDegree G v : ℝ)⁻¹ * ∑ e : G.Dart, if e.fst = v then returnRow G t v e else 0) *
    ((excessDegree G v : ℝ)⁻¹ * ∑ f : G.Dart, if f.fst = v then returnRow G s v f else 0)
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs with he
  · apply Finset.sum_congr rfl
    intro f _
    split_ifs <;> ring
  · simp

theorem collision_power_sum_le_returns (t s : ℕ) (ht : 1 ≤ t) (hs : 1 ≤ s) :
    (∑ e : G.Dart, ∑ f : G.Dart, if e.fst = f.fst then
      (transition G ^ t) e f * (transition G ^ s) f e else 0) ≤
      ∑ v : V, returnMass G t v * returnMass G s v := by
  classical
  rw [sum_same_fst_eq_vertex_sum]
  apply Finset.sum_le_sum
  intro v _
  rw [← sum_returnRows_eq_product]
  apply Finset.sum_le_sum
  intro e _
  split_ifs with he
  · apply Finset.sum_le_sum
    intro f _
    split_ifs with hf
    · apply mul_le_mul
      · simpa only [hf] using transition_pow_le_returnRow G t ht e f
      · simpa only [he] using transition_pow_le_returnRow G s hs f e
      · exact Matrix.pow_apply_nonneg (transition_nonneg G) s f e
      · exact mul_nonneg (by positivity) (returnRow_nonneg G t v e)
    · exact le_rfl
  · exact le_rfl

/-- Failure of the actual simple-cycle conclusion forces the ordered
collision bound. Both cuts allow arbitrary closing seams. -/
theorem trace_le_return_collisions_of_no_cycle (n : ℕ) (hL : 3 ≤ n + 1)
    (hno : ¬ HasCycleLength G (n + 1)) :
    Matrix.trace (transition G ^ (n + 1)) ≤ (n + 1 : ℝ) *
      ∑ t : Fin (n + 1), if t ≠ 0 then
        ∑ v : V, returnMass G t.val v * returnMass G (n + 1 - t.val) v else 0 := by
  classical
  have hrep : ∀ w : Fin (n + 1) → G.Dart, 0 < matrixCycleProduct (transition G) n w →
      ¬ Function.Injective (fun k => (w k).fst) := by
    intro w hp hi
    exact hno (positive_simple_word_has_cycle G n hL w hp hi)
  have h := trace_pow_le_ordered_collision_sum (transition G) (transition_nonneg G)
    (fun e : G.Dart => e.fst) n hrep
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro t _
  split_ifs with ht
  · rw [cycle_collision_sum_eq_powers (transition G) (fun e : G.Dart => e.fst) n t ht]
    exact collision_power_sum_le_returns G t.val (n + 1 - t.val)
      (by have := Fin.val_ne_zero_iff.mpr ht; omega) (by have := t.isLt; omega)
  · exact le_rfl

end GirthVerification
