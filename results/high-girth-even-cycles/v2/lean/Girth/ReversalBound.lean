import Girth.NonBacktracking
import Girth.LocalBlock

namespace GirthVerification

open scoped BigOperators

theorem localBlock_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) (i : ι) :
    localBlock x i = ∑ j, if j = i then 0 else x j / ((Fintype.card ι : ℝ) - 1) := by
  simp [localBlock, Finset.sum_ite, Finset.filter_ne', Finset.sum_erase_eq_sub,
    ← Finset.sum_div, sub_div]

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def incomingDart (v : V) (w : G.neighborSet v) : G.Dart := ⟨(w, v), w.property.symm⟩

def incomingCoordinates : (Σ v : V, G.neighborSet v) ≃ G.Dart :=
  { toFun := fun vi => incomingDart G vi.1 vi.2
    invFun := fun e => ⟨e.snd, e.fst, e.adj.symm⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

omit [DecidableEq V] in
theorem sum_incoming (f : G.Dart → ℝ) :
    ∑ e, f e = ∑ v, ∑ i : G.neighborSet v, f (incomingDart G v i) := by
  rw [← (incomingCoordinates G).sum_comp]
  exact Fintype.sum_sigma _

noncomputable def reversalBlock : Matrix G.Dart G.Dart ℝ := transition G * reversal G

theorem reversalBlock_apply (e f : G.Dart) :
    reversalBlock G e f =
      if e.snd = f.snd ∧ e ≠ f then 1 / (excessDegree G e.snd : ℝ) else 0 := by
  classical
  rw [reversalBlock, mul_reversal]
  have hne : f.symm ≠ e.symm ↔ e ≠ f := by
    constructor
    · intro h he; subst f; exact h rfl
    · intro h he
      apply h
      simpa using (congrArg SimpleGraph.Dart.symm he).symm
  simp only [transition, NonBacktracking, hne]
  rfl

theorem reversalBlock_mulVec_incoming (hdeg : MinimumDegreeThree G)
    (x : G.Dart → ℝ) (v : V) (i : G.neighborSet v) :
    (reversalBlock G).mulVec x (incomingDart G v i) =
      localBlock (fun j : G.neighborSet v => x (incomingDart G v j)) i := by
  classical
  rw [Matrix.mulVec, dotProduct, sum_incoming]
  have hd : (excessDegree G v : ℝ) = (Fintype.card (G.neighborSet v) : ℝ) - 1 := by
    rw [G.card_neighborSet_eq_degree]
    dsimp [excessDegree]
    rw [Nat.cast_sub (by have := hdeg v; omega)]
    norm_num
  have hinj : Function.Injective (incomingDart G v) := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun e : G.Dart => e.fst) h
  have hi : ∀ w : V,
      (∑ j : G.neighborSet w, reversalBlock G (incomingDart G v i) (incomingDart G w j) *
        x (incomingDart G w j)) =
      if w = v then (∑ j : G.neighborSet v,
        if j = i then 0 else x (incomingDart G v j) /
          ((Fintype.card (G.neighborSet v) : ℝ) - 1)) else 0 := by
    intro w
    by_cases hw : w = v
    · subst w
      rw [if_pos rfl]
      apply Finset.sum_congr rfl
      intro j _
      rw [reversalBlock_apply]
      change (if v = v ∧ incomingDart G v i ≠ incomingDart G v j then
        1 / (excessDegree G v : ℝ) else 0) * x (incomingDart G v j) = _
      rw [hd]
      have heq : incomingDart G v i = incomingDart G v j ↔ j = i :=
        ⟨fun h => (hinj h).symm, fun h => congrArg (incomingDart G v) h.symm⟩
      by_cases hj : j = i <;> simp [heq, hj, div_eq_mul_inv, mul_comm]
    · rw [if_neg hw]
      apply Finset.sum_eq_zero
      intro j _
      rw [reversalBlock_apply]
      simp [incomingDart, Ne.symm hw]
  simp_rw [hi]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ v), localBlock_eq_sum]

/-- The full graph quadratic bound, with every incoming block using its own
degree. This is the first inequality in display (3) of the manuscript. -/
theorem reversalBlock_square_le (hdeg : MinimumDegreeThree G) (x : G.Dart → ℝ) :
    ∑ e, ((reversalBlock G).mulVec x e) ^ 2 ≤ (1 / 2 : ℝ) *
      ((∑ e, x e ^ 2) + ∑ e, x e * (reversalBlock G).mulVec x e) := by
  rw [sum_incoming, sum_incoming, sum_incoming]
  simp_rw [reversalBlock_mulVec_incoming G hdeg]
  calc
    _ ≤ ∑ v, (1 / 2 : ℝ) *
        ((∑ i : G.neighborSet v, x (incomingDart G v i) ^ 2) +
          ∑ i : G.neighborSet v, x (incomingDart G v i) *
            localBlock (fun j : G.neighborSet v => x (incomingDart G v j)) i) := by
      apply Finset.sum_le_sum
      intro v _
      apply localBlock_square_le
      simpa [G.card_neighborSet_eq_degree] using hdeg v
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]

theorem reversal_mulVec (x : G.Dart → ℝ) (e : G.Dart) :
    (reversal G).mulVec x e = x e.symm := by
  classical
  simp [Matrix.mulVec, dotProduct, reversal]

theorem reversalBlock_mulVec_reverse (x : G.Dart → ℝ) :
    (reversalBlock G).mulVec (fun e => x e.symm) = (transition G).mulVec x := by
  have hJ : (reversal G).mulVec (fun e => x e.symm) = x := by
    ext e
    simp [reversal_mulVec]
  rw [reversalBlock, ← Matrix.mulVec_mulVec, hJ]

theorem reversal_mul_transition_isHermitian : (reversal G * transition G).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro e f
  rw [reversal_mul, reversal_mul]
  simpa using transition_reverse G e.symm f

/-- The actual non-backtracking graph operator satisfies the crucial
quadratic inequality, equivalent to `P*P ≤ (I+JP)/2`. -/
theorem transition_quadratic_bound (hdeg : MinimumDegreeThree G) (x : G.Dart → ℝ) :
    ∑ e, ((transition G).mulVec x e) ^ 2 ≤ (1 / 2 : ℝ) *
      ((∑ e, x e ^ 2) + ∑ e, x e * (reversal G * transition G).mulVec x e) := by
  have h := reversalBlock_square_le G hdeg (fun e => x e.symm)
  rw [reversalBlock_mulVec_reverse] at h
  have hn : (∑ e : G.Dart, x e.symm ^ 2) = ∑ e : G.Dart, x e ^ 2 :=
    (reverseEquiv G).sum_comp (fun e => x e ^ 2)
  have hi : (∑ e : G.Dart, x e.symm * (transition G).mulVec x e) =
      ∑ e : G.Dart, x e * (reversal G * transition G).mulVec x e := by
    have hi' := (reverseEquiv G).sum_comp
      (fun e => x e * (transition G).mulVec x e.symm)
    simpa [← Matrix.mulVec_mulVec, reversal_mulVec, reverseEquiv] using hi'
  rwa [hn, hi] at h

end GirthVerification
