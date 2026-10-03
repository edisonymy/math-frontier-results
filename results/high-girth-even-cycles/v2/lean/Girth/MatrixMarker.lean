import Girth.CollisionUnion

namespace GirthVerification

theorem sum_matrixPathProduct_marker {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (A : Matrix ι ι ℝ) (color : ι → α) (v : α) (n : ℕ) (e f : ι) (i : Fin n) :
    (∑ w : Fin n → ι, if color (w i) = v then matrixPathProduct A n e f w else 0) =
      ∑ g : ι, if color g = v then (A ^ (i.val + 1)) e g * (A ^ (n - i.val)) g f else 0 := by
  classical
  induction n generalizing e with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [sum_fin_succ_functions]
      simp only [Fin.cons_zero, matrixPathProduct, Fin.tail_cons, Fin.val_zero, zero_add,
        Nat.sub_zero, pow_one]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : color g = v
      · simp [hg, ← Finset.mul_sum, sum_matrixPathProduct]
      · simp [hg]
    · rw [sum_fin_succ_functions]
      simp only [Fin.cons_succ, matrixPathProduct, Fin.cons_zero, Fin.tail_cons, Fin.val_succ,
        Nat.add_sub_add_right]
      have hfactor : ∀ k : ι,
          (∑ w : Fin n → ι, if color (w j) = v then A e k * matrixPathProduct A n k f w else 0) =
          A e k * (∑ w : Fin n → ι, if color (w j) = v then matrixPathProduct A n k f w else 0) := by
        intro k
        simp [Finset.mul_sum, mul_ite]
      simp_rw [hfactor, ih, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : color g = v
      · simp only [hg, if_true]
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul]
        have hmul : (∑ k : ι, A e k * (A ^ (j.val + 1)) k g) =
            (A ^ (j.val + 1 + 1)) e g := by
          conv_rhs => rw [pow_succ', Matrix.mul_apply]
        rw [hmul]
      · simp [hg]

/-- Marking a second vertex splits a cyclic word sum into two matrix powers. -/
theorem cycle_collision_sum_eq_powers {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (A : Matrix ι ι ℝ) (color : ι → α) (n : ℕ) (t : Fin (n + 1)) (ht : t ≠ 0) :
    (∑ w : Fin (n + 1) → ι,
      if color (w 0) = color (w t) then matrixCycleProduct A n w else 0) =
      ∑ e : ι, ∑ f : ι, if color e = color f then
        (A ^ t.val) e f * (A ^ (n + 1 - t.val)) f e else 0 := by
  classical
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero ht
  rw [sum_fin_succ_functions]
  simp only [Fin.cons_zero, Fin.cons_succ, matrixCycleProduct, Fin.tail_cons, Fin.val_succ,
    Nat.add_sub_add_right]
  apply Finset.sum_congr rfl
  intro e _
  simpa only [eq_comm] using sum_matrixPathProduct_marker A color (color e) n e e i

end GirthVerification
