import Girth.GraphBounds
import Mathlib.Algebra.Order.Field.GeomSum

namespace GirthVerification

theorem finite_geometric_tail_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (hinj : Set.InjOn f s) (g L : ℕ) (hlo : ∀ i ∈ s, g ≤ f i) (hhi : ∀ i ∈ s, f i < L)
    (q : ℝ) (hq : 0 ≤ q) (hqone : q < 1) :
    ∑ i ∈ s, q ^ f i ≤ q ^ g / (1 - q) := by
  have hsub : s.image f ⊆ Finset.Ico g L := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Ico.mpr ⟨hlo i hi, hhi i hi⟩
  calc
    _ = ∑ k ∈ s.image f, q ^ k := (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ Finset.Ico g L, q ^ k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hq _)
    _ ≤ _ := geom_sum_Ico_le_of_lt_one hq hqone

def collisionTimes (L g : ℕ) : Finset (Fin L) :=
  Finset.univ.filter (fun t => 0 < t.val ∧ g ≤ t.val ∧ g ≤ L - t.val)

theorem collisionTimes_card_le (L g : ℕ) : (collisionTimes L g).card ≤ L := by
  unfold collisionTimes
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

theorem collisionTimes_geometric_sum_le (L g : ℕ) (q : ℝ) (hq : 0 ≤ q) (hqone : q < 1) :
    (∑ t ∈ collisionTimes L g, (q ^ t.val + q ^ (L - t.val))) ≤ 2 * q ^ g / (1 - q) := by
  have h1 := finite_geometric_tail_le (collisionTimes L g) (fun t : Fin L => t.val)
    (fun _ _ _ _ h => Fin.ext h) g L
    (fun t ht => (Finset.mem_filter.mp ht).2.2.1)
    (fun t _ => t.isLt) q hq hqone
  have h2 := finite_geometric_tail_le (collisionTimes L g) (fun t : Fin L => L - t.val)
    (by
      intro a _ b _ hab
      apply Fin.ext
      have ha := a.isLt
      have hb := b.isLt
      dsimp only at hab
      omega) g L
    (fun t ht => (Finset.mem_filter.mp ht).2.2.2)
    (by
      intro t ht
      have hn := (Finset.mem_filter.mp ht).2.1
      have hti := t.isLt
      change L - t.val < L
      omega) q hq hqone
  rw [Finset.sum_add_distrib]
  dsimp only at h1 h2
  have he : 2 * q ^ g / (1 - q) = q ^ g / (1 - q) + q ^ g / (1 - q) := by ring
  rw [he]
  exact add_le_add h1 h2

end GirthVerification
