import Girth.FiniteMoments

namespace GirthVerification

theorem weighted_moment_product_le {ι : Type*} [Fintype ι] (W a : ι → ℝ)
    (hW : ∀ i, 0 ≤ W i) (ha : ∀ i, 0 ≤ a i) (M : ℝ) (hM : ∑ i, W i ≤ M)
    (t s : ℕ) (ht : 0 < t) (hs : 0 < s) :
    (∑ i, W i * a i ^ t) * (∑ i, W i * a i ^ s) ≤
      M * ∑ i, W i * a i ^ (t + s) := by
  let θ : ℝ := (t : ℝ) / (t + s : ℕ)
  let φ : ℝ := (s : ℝ) / (t + s : ℕ)
  have hL : (0 : ℝ) < (t + s : ℕ) := by exact_mod_cast (by omega : 0 < t + s)
  have hθφ : θ + φ = 1 := by dsimp [θ, φ]; push_cast; field_simp
  have hpoly : ∀ i j, W i * W j * (θ * a i ^ (t + s) + φ * a j ^ (t + s)) =
      (θ * (W i * a i ^ (t + s))) * W j + W i * (φ * (W j * a j ^ (t + s))) := by
    intro i j
    ring
  have hfactor : (∑ i, ∑ j, W i * W j * (θ * a i ^ (t + s) + φ * a j ^ (t + s))) =
      (∑ i, W i) * (∑ i, W i * a i ^ (t + s)) := by
    simp_rw [hpoly, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [← Finset.mul_sum]
    calc
      _ = (θ + φ) * (∑ i, W i) * (∑ i, W i * a i ^ (t + s)) := by ring
      _ = _ := by rw [hθφ, one_mul]
  calc
    _ = ∑ i, ∑ j, W i * W j * (a i ^ t * a j ^ s) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i, ∑ j, W i * W j * (θ * a i ^ (t + s) + φ * a j ^ (t + s)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (weighted_young_nat_powers _ _ (ha i) (ha j) t s ht hs)
        (mul_nonneg (hW i) (hW j))
    _ = (∑ i, W i) * (∑ i, W i * a i ^ (t + s)) := hfactor
    _ ≤ _ := mul_le_mul_of_nonneg_right hM (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (hW i) (pow_nonneg (ha i) _)))

/-- Summed weighted Young inequality (17). Row mass and column mass are
the only kernel hypotheses; the graph supplies both bounds separately. -/
theorem sum_weighted_moment_products_le {α ι : Type*} [Fintype α] [Fintype ι]
    (W : α → ι → ℝ) (a : ι → ℝ) (hW : ∀ v i, 0 ≤ W v i) (ha : ∀ i, 0 ≤ a i)
    (M C : ℝ) (hM : ∀ v, ∑ i, W v i ≤ M) (hC : ∀ i, ∑ v, W v i ≤ C)
    (hMpos : 0 ≤ M) (t s : ℕ) (ht : 0 < t) (hs : 0 < s) :
    ∑ v, (∑ i, W v i * a i ^ t) * (∑ i, W v i * a i ^ s) ≤
      C * M * ∑ i, a i ^ (t + s) := by
  calc
    _ ≤ ∑ v, M * ∑ i, W v i * a i ^ (t + s) :=
      Finset.sum_le_sum (fun v _ => weighted_moment_product_le (W v) a (hW v) ha M (hM v) t s ht hs)
    _ = M * ∑ i, (∑ v, W v i) * a i ^ (t + s) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
    _ ≤ M * ∑ i, C * a i ^ (t + s) := by
      apply mul_le_mul_of_nonneg_left _ hMpos
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hC i) (pow_nonneg (ha i) _)
    _ = _ := by rw [← Finset.mul_sum]; ring

end GirthVerification
