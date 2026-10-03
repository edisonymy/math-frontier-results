import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace GirthVerification

theorem sum_fin_succ_functions {ι M : Type*} [Fintype ι] [AddCommMonoid M] (n : ℕ)
    (F : (Fin (n + 1) → ι) → M) :
    ∑ w, F w = ∑ e : ι, ∑ w : Fin n → ι, F (Fin.cons e w) := by
  classical
  have h := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => ι))
    (fun p : ι × (Fin n → ι) => F (Fin.cons p.1 p.2)) F (fun _ => rfl)
  simpa only [Fintype.sum_prod_type] using h.symm

def matrixPathProduct {ι R : Type*} [Semiring R] (A : Matrix ι ι R) :
    (n : ℕ) → ι → ι → (Fin n → ι) → R
  | 0, e, f, _ => A e f
  | n + 1, e, f, w => A e (w 0) * matrixPathProduct A n (w 0) f (Fin.tail w)

theorem sum_matrixPathProduct {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]
    (A : Matrix ι ι R) (n : ℕ) (e f : ι) :
    ∑ w : Fin n → ι, matrixPathProduct A n e f w = (A ^ (n + 1)) e f := by
  classical
  induction n generalizing e with
  | zero => simp [matrixPathProduct]
  | succ n ih =>
    rw [sum_fin_succ_functions]
    simp only [matrixPathProduct, Fin.cons_zero, Fin.tail_cons, ← Finset.mul_sum, ih]
    conv_rhs => rw [pow_succ', Matrix.mul_apply]

def matrixCycleProduct {ι R : Type*} [Semiring R] (A : Matrix ι ι R) (n : ℕ)
    (w : Fin (n + 1) → ι) : R := matrixPathProduct A n (w 0) (w 0) (Fin.tail w)

theorem trace_pow_eq_sum_matrixCycleProduct {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]
    (A : Matrix ι ι R) (n : ℕ) :
    Matrix.trace (A ^ (n + 1)) = ∑ w : Fin (n + 1) → ι, matrixCycleProduct A n w := by
  rw [sum_fin_succ_functions]
  simp only [matrixCycleProduct, Fin.cons_zero, Fin.tail_cons, sum_matrixPathProduct, Matrix.trace, Matrix.diag]

theorem snoc_succ_eq_tail_snoc {ι : Type*} (n : ℕ) (w : Fin (n + 1) → ι) (f : ι) (k : Fin (n + 1)) :
    Fin.snoc (α := fun _ : Fin (n + 2) => ι) w f k.succ =
      Fin.snoc (α := fun _ : Fin (n + 1) => ι) (Fin.tail w) f k := by
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [Fin.succ_last]
  · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    rfl

theorem matrixPathProduct_eq_prod {ι R : Type*} [CommSemiring R] (A : Matrix ι ι R)
    (n : ℕ) (e f : ι) (w : Fin n → ι) :
    matrixPathProduct A n e f w = ∏ k : Fin (n + 1),
      A (Fin.cons (α := fun _ : Fin (n + 1) => ι) e w k)
        (Fin.snoc (α := fun _ : Fin (n + 1) => ι) w f k) := by
  induction n generalizing e with
  | zero => simp [matrixPathProduct, Fin.snoc_zero]
  | succ n ih =>
    rw [matrixPathProduct, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.snoc_apply_zero, Fin.cons_succ]
    rw [ih]
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    rw [snoc_succ_eq_tail_snoc, Fin.cons_self_tail]

end GirthVerification
