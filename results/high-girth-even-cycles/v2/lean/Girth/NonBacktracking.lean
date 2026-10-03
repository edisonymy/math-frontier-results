import Girth.GraphBounds
import Mathlib.LinearAlgebra.Matrix.Hermitian

namespace GirthVerification

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def NonBacktracking (e f : G.Dart) : Prop := e.snd = f.fst ∧ f ≠ e.symm

instance (e f : G.Dart) : Decidable (NonBacktracking G e f) := by
  unfold NonBacktracking
  infer_instance

def excessDegree (v : V) : ℕ := G.degree v - 1

noncomputable def transition : Matrix G.Dart G.Dart ℝ := by
  classical
  exact fun e f => if NonBacktracking G e f then 1 / (excessDegree G e.snd : ℝ) else 0

noncomputable def reversal : Matrix G.Dart G.Dart ℝ := by
  classical
  exact fun e f => if f = e.symm then 1 else 0

def reverseEquiv : G.Dart ≃ G.Dart :=
  { toFun := SimpleGraph.Dart.symm
    invFun := SimpleGraph.Dart.symm
    left_inv := SimpleGraph.Dart.symm_symm
    right_inv := SimpleGraph.Dart.symm_symm }

omit [DecidableEq V] in
theorem excessDegree_ge_two (hdeg : MinimumDegreeThree G) (v : V) :
    2 ≤ excessDegree G v := by
  have := hdeg v
  dsimp [excessDegree]
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem nonBacktracking_reverse_iff (e f : G.Dart) :
    NonBacktracking G f.symm e.symm ↔ NonBacktracking G e f := by
  simp only [NonBacktracking, SimpleGraph.Dart.symm_symm]
  change (f.fst = e.snd ∧ e.symm ≠ f) ↔ (e.snd = f.fst ∧ f ≠ e.symm)
  simp only [eq_comm, ne_comm]

theorem transition_reverse (e f : G.Dart) :
    transition G f.symm e.symm = transition G e f := by
  classical
  simp only [transition, nonBacktracking_reverse_iff]
  by_cases h : NonBacktracking G e f
  · simp only [h, if_true]
    change 1 / (excessDegree G f.fst : ℝ) = 1 / (excessDegree G e.snd : ℝ)
    rw [h.1]
  · simp [h]

theorem nonBacktracking_successors (e : G.Dart) :
    ({f : G.Dart | NonBacktracking G e f} : Finset _) =
      ({f : G.Dart | f.fst = e.snd} : Finset _).erase e.symm := by
  classical
  ext f
  simp [NonBacktracking, eq_comm, and_comm]

theorem card_nonBacktracking_successors (e : G.Dart) :
    ({f : G.Dart | NonBacktracking G e f} : Finset _).card = excessDegree G e.snd := by
  classical
  rw [nonBacktracking_successors, Finset.card_erase_of_mem (by simp),
    G.dart_fst_fiber_card_eq_degree]
  rfl

theorem transition_nonneg (e f : G.Dart) : 0 ≤ transition G e f := by
  classical
  unfold transition
  split_ifs <;> positivity

theorem transition_row_sum (hdeg : MinimumDegreeThree G) (e : G.Dart) :
    ∑ f : G.Dart, transition G e f = 1 := by
  classical
  have hq : (excessDegree G e.snd : ℝ) ≠ 0 := by
    have := excessDegree_ge_two G hdeg e.snd
    exact_mod_cast (by omega : excessDegree G e.snd ≠ 0)
  simp only [transition, ← Finset.sum_filter]
  rw [Finset.sum_const, card_nonBacktracking_successors]
  simp [nsmul_eq_mul, hq]

theorem transition_column_sum (hdeg : MinimumDegreeThree G) (f : G.Dart) :
    ∑ e : G.Dart, transition G e f = 1 := by
  calc
    ∑ e : G.Dart, transition G e f = ∑ e : G.Dart, transition G f.symm e.symm := by
      apply Finset.sum_congr rfl
      intro e _
      exact (transition_reverse G e f).symm
    _ = ∑ e : G.Dart, transition G f.symm e := (reverseEquiv G).sum_comp _
    _ = 1 := transition_row_sum G hdeg f.symm

theorem mul_reversal (A : Matrix G.Dart G.Dart ℝ) (e f : G.Dart) :
    (A * reversal G) e f = A e f.symm := by
  classical
  simp only [Matrix.mul_apply, reversal]
  have hf : ∀ x : G.Dart, f = x.symm ↔ x = f.symm := by
    intro x
    constructor <;> intro h
    · simpa using (congrArg SimpleGraph.Dart.symm h).symm
    · subst x; simp
  simp [hf]

theorem reversal_mul (A : Matrix G.Dart G.Dart ℝ) (e f : G.Dart) :
    (reversal G * A) e f = A e.symm f := by
  classical
  simp [Matrix.mul_apply, reversal]

theorem reversal_sq : reversal G * reversal G = 1 := by
  classical
  ext e f
  rw [mul_reversal]
  have heq : e.symm = f.symm ↔ e = f :=
    ⟨fun h => by simpa using congrArg SimpleGraph.Dart.symm h,
      congrArg SimpleGraph.Dart.symm⟩
  simp [reversal, Matrix.one_apply, heq, eq_comm]

omit [Fintype V] [DecidableRel G.Adj] in
theorem reversal_isHermitian : (reversal G).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro e f
  have hf : e = f.symm ↔ f = e.symm := by
    constructor <;> intro h
    · simpa using (congrArg SimpleGraph.Dart.symm h).symm
    · simpa using (congrArg SimpleGraph.Dart.symm h).symm
  simp [reversal, hf]

theorem transition_mul_reversal_isHermitian : (transition G * reversal G).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro e f
  rw [mul_reversal, mul_reversal]
  simpa using transition_reverse G e f.symm

theorem transition_transpose : (transition G).transpose = reversal G * transition G * reversal G := by
  ext e f
  rw [mul_reversal, reversal_mul]
  exact (transition_reverse G f e).symm

end GirthVerification
