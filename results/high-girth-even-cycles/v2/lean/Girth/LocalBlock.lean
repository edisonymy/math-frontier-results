import Girth.GraphBounds

namespace GirthVerification

open scoped BigOperators

/-- The local reversal block on a vertex of degree `card ι`.
Its diagonal is zero and each off-diagonal entry is `1 / (card ι - 1)`. -/
noncomputable def localBlock {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) : ℝ :=
  ((∑ j, x j) - x i) / ((Fintype.card ι : ℝ) - 1)

/-- The quadratic inequality in display (3), proved directly by Cauchy–Schwarz
on each incoming-edge block. No block diagonalization is assumed. -/
theorem localBlock_square_le {ι : Type*} [Fintype ι] (hd : 3 ≤ Fintype.card ι)
    (x : ι → ℝ) :
    ∑ i, localBlock x i ^ 2 ≤ (1 / 2 : ℝ) *
      ((∑ i, x i ^ 2) + ∑ i, x i * localBlock x i) := by
  let d : ℝ := Fintype.card ι
  let S : ℝ := ∑ i, x i
  let T : ℝ := ∑ i, x i ^ 2
  have hdr : 3 ≤ d := by dsimp [d]; exact_mod_cast hd
  have hq : d - 1 ≠ 0 := by linarith
  have hqpos : 0 < (d - 1) ^ 2 := sq_pos_of_ne_zero hq
  have hCS : S ^ 2 ≤ d * T := by
    simpa [S, T, d] using
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun _ => (1 : ℝ)) x
  have hB : (∑ i, (S - x i) ^ 2) = (d - 2) * S ^ 2 + T := by
    simp_rw [show ∀ i, (S - x i) ^ 2 = S ^ 2 - 2 * S * x i + x i ^ 2 by
      intro i; ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change d * S ^ 2 - 2 * S * S + T = _
    ring
  have hC : (∑ i, x i * (S - x i)) = S ^ 2 - T := by
    simp_rw [mul_sub, ← sq]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    change S * S - T = _
    ring
  have hleft : (∑ i, localBlock x i ^ 2) = ((d - 2) * S ^ 2 + T) / (d - 1) ^ 2 := by
    simp only [localBlock, div_pow]
    rw [← Finset.sum_div, hB]
  have hright : (∑ i, x i * localBlock x i) = (S ^ 2 - T) / (d - 1) := by
    simp only [localBlock, ← mul_div_assoc]
    rw [← Finset.sum_div, hC]
  rw [hleft, hright]
  change ((d - 2) * S ^ 2 + T) / (d - 1) ^ 2 ≤
    (1 / 2 : ℝ) * (T + (S ^ 2 - T) / (d - 1))
  apply (div_le_iff₀ hqpos).mpr
  have hr : ((1 / 2 : ℝ) * (T + (S ^ 2 - T) / (d - 1))) * (d - 1) ^ 2 =
      ((d - 2) * S ^ 2 + T) + (d - 3) * (d * T - S ^ 2) / 2 := by
    field_simp; ring
  rw [hr]
  have hprod : 0 ≤ (d - 3) * (d * T - S ^ 2) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hCS)
  linarith

end GirthVerification
