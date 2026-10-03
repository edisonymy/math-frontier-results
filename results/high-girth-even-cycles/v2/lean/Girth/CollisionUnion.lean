import Girth.CyclicWords
import Girth.GraphBounds

namespace GirthVerification

theorem matrixCycleProduct_nonneg {ι : Type*} (A : Matrix ι ι ℝ)
    (hA : ∀ e f, 0 ≤ A e f) (n : ℕ) (w : Fin (n + 1) → ι) :
    0 ≤ matrixCycleProduct A n w := by
  rw [matrixCycleProduct_eq_prod]
  exact Finset.prod_nonneg (fun k _ => hA _ _)

theorem cycle_collision_sum_rotation {ι α : Type*} [Fintype ι] [DecidableEq α] (A : Matrix ι ι ℝ)
    (color : ι → α) (n : ℕ) (a t : Fin (n + 1)) :
    (∑ w : Fin (n + 1) → ι,
      if color (w a) = color (w (a + t)) then matrixCycleProduct A n w else 0) =
    ∑ w : Fin (n + 1) → ι,
      if color (w 0) = color (w t) then matrixCycleProduct A n w else 0 := by
  classical
  exact Fintype.sum_equiv (rotateWordEquiv n a) _ _ (fun w => by
    simp [rotateWordEquiv, rotateWord, matrixCycleProduct_rotate])

/-- If every positive cyclic word repeats a color, its total weight is
bounded by all ordered collision charges. This intentionally keeps the
factor `L` and avoids choosing an unordered pair. -/
theorem trace_pow_le_ordered_collision_sum {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α]
    (A : Matrix ι ι ℝ) (hA : ∀ e f, 0 ≤ A e f) (color : ι → α) (n : ℕ)
    (hrep : ∀ w : Fin (n + 1) → ι, 0 < matrixCycleProduct A n w →
      ¬ Function.Injective (fun k => color (w k))) :
    Matrix.trace (A ^ (n + 1)) ≤ (n + 1 : ℝ) *
      ∑ t : Fin (n + 1), if t ≠ 0 then
        ∑ w : Fin (n + 1) → ι,
          if color (w 0) = color (w t) then matrixCycleProduct A n w else 0 else 0 := by
  classical
  have hpoint : ∀ w : Fin (n + 1) → ι, matrixCycleProduct A n w ≤
      ∑ a : Fin (n + 1), ∑ t : Fin (n + 1), if t ≠ 0 then
        if color (w a) = color (w (a + t)) then matrixCycleProduct A n w else 0 else 0 := by
    intro w
    have hn := matrixCycleProduct_nonneg A hA n w
    have hterms : ∀ a t : Fin (n + 1), 0 ≤
        (if t ≠ 0 then if color (w a) = color (w (a + t)) then matrixCycleProduct A n w else 0 else 0) := by
      intro a t
      split_ifs <;> positivity
    by_cases hp : 0 < matrixCycleProduct A n w
    · have hd := hrep w hp
      simp only [Function.Injective] at hd
      push_neg at hd
      obtain ⟨a, b, heq, hne⟩ := hd
      let t : Fin (n + 1) := b - a
      have ht : t ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have ha : a + t = b := by dsimp [t]; abel
      have hinner := Finset.single_le_sum (s := Finset.univ) (fun t _ => hterms a t) (Finset.mem_univ t)
      have houter := Finset.single_le_sum (s := Finset.univ)
        (f := fun a : Fin (n + 1) => ∑ t : Fin (n + 1), if t ≠ 0 then
          if color (w a) = color (w (a + t)) then matrixCycleProduct A n w else 0 else 0)
        (fun a _ => Finset.sum_nonneg (s := Finset.univ) (fun t _ => hterms a t)) (Finset.mem_univ a)
      have hterm : (if t ≠ 0 then if color (w a) = color (w (a + t)) then
          matrixCycleProduct A n w else 0 else 0) = matrixCycleProduct A n w := by
        rw [if_pos ht, ha, if_pos heq]
      rw [hterm] at hinner
      exact hinner.trans houter
    · have hz : matrixCycleProduct A n w = 0 := by linarith
      rw [hz]
      simp
  rw [trace_pow_eq_sum_matrixCycleProduct]
  calc
    _ ≤ ∑ w : Fin (n + 1) → ι, ∑ a : Fin (n + 1), ∑ t : Fin (n + 1),
        if t ≠ 0 then if color (w a) = color (w (a + t)) then matrixCycleProduct A n w else 0 else 0 :=
      Finset.sum_le_sum (fun w _ => hpoint w)
    _ = ∑ a : Fin (n + 1), ∑ t : Fin (n + 1), if t ≠ 0 then
        ∑ w : Fin (n + 1) → ι,
          if color (w a) = color (w (a + t)) then matrixCycleProduct A n w else 0 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> simp
    _ = _ := by
      simp_rw [cycle_collision_sum_rotation]
      simp [nsmul_eq_mul]

end GirthVerification
