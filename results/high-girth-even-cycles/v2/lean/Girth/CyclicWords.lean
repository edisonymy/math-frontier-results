import Girth.MatrixWords
import Mathlib.Algebra.Group.Fin.Basic

namespace GirthVerification

theorem fin_last_add_one (n : ℕ) : (Fin.last n : Fin (n + 1)) + 1 = 0 := by
  apply Fin.ext
  cases n with
  | zero => simp
  | succ n =>
    simp only [Fin.val_add, Fin.val_last, Fin.val_one]
    simp

theorem fin_castSucc_add_one (n : ℕ) (i : Fin n) : (i.castSucc : Fin (n + 1)) + 1 = i.succ := by
  apply Fin.ext
  have hn : 1 < n + 1 := by have := i.isLt; omega
  simp only [Fin.val_add, Fin.val_castSucc, Fin.val_one', Fin.val_succ]
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by have := i.isLt; omega)]

theorem snoc_tail_eq_cyclic_next {ι : Type*} (n : ℕ) (w : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    Fin.snoc (α := fun _ : Fin (n + 1) => ι) (Fin.tail w) (w 0) k = w (k + 1) := by
  refine Fin.lastCases ?_ (fun i => ?_) k
  · rw [Fin.snoc_last, fin_last_add_one]
  · rw [Fin.snoc_castSucc, fin_castSucc_add_one]
    rfl

theorem matrixCycleProduct_eq_prod {ι R : Type*} [CommSemiring R] (A : Matrix ι ι R)
    (n : ℕ) (w : Fin (n + 1) → ι) :
    matrixCycleProduct A n w = ∏ k : Fin (n + 1), A (w k) (w (k + 1)) := by
  rw [matrixCycleProduct, matrixPathProduct_eq_prod, Fin.cons_self_tail]
  apply Finset.prod_congr rfl
  intro k _
  rw [snoc_tail_eq_cyclic_next]

def rotateWord {ι : Type*} (n : ℕ) (a : Fin (n + 1)) (w : Fin (n + 1) → ι) : Fin (n + 1) → ι :=
  fun k => w (a + k)

theorem matrixCycleProduct_rotate {ι R : Type*} [CommSemiring R] (A : Matrix ι ι R)
    (n : ℕ) (a : Fin (n + 1)) (w : Fin (n + 1) → ι) :
    matrixCycleProduct A n (rotateWord n a w) = matrixCycleProduct A n w := by
  simp only [matrixCycleProduct_eq_prod, rotateWord, ← add_assoc]
  exact Fintype.prod_equiv (Equiv.addLeft a) _ _ (fun _ => rfl)

def rotateWordEquiv {ι : Type*} (n : ℕ) (a : Fin (n + 1)) :
    (Fin (n + 1) → ι) ≃ (Fin (n + 1) → ι) where
  toFun := rotateWord n a
  invFun := rotateWord n (-a)
  left_inv w := by funext k; simp [rotateWord, ← add_assoc]
  right_inv w := by funext k; simp [rotateWord, ← add_assoc]

end GirthVerification
