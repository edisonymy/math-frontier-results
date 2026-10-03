import Girth.CollisionReturns
import Girth.ReturnProducts
import Girth.GeometricTail
import Girth.TraceEstimate

namespace GirthVerification

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem return_collision_sum_eq_restricted (n g : ℕ) (hg : g ≤ G.girth) :
    (∑ t : Fin (n + 1), if t ≠ 0 then
      ∑ v : V, returnMass G t.val v * returnMass G (n + 1 - t.val) v else 0) =
      ∑ t ∈ collisionTimes (n + 1) g,
        ∑ v : V, returnMass G t.val v * returnMass G (n + 1 - t.val) v := by
  classical
  unfold collisionTimes
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : t = 0
  · simp [ht]
  have hp : 0 < t.val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr ht)
  have hs : 1 ≤ n + 1 - t.val := by have := t.isLt; omega
  rw [if_pos ht]
  by_cases hgt : g ≤ t.val
  · by_cases hgs : g ≤ n + 1 - t.val
    · simp [ht, hp, hgt, hgs]
    · simp only [ht, if_true, hp, hgt, hgs, and_false, if_false]
      apply Finset.sum_eq_zero
      intro v _
      rw [returnMass_eq_zero_below_girth G (n + 1 - t.val) hs (by omega) v, mul_zero]
  · simp only [ht, if_true, hp, hgt, false_and, and_false, if_false]
    apply Finset.sum_eq_zero
    intro v _
    rw [returnMass_eq_zero_below_girth G t.val (by omega) (by omega) v, zero_mul]

theorem return_collision_sum_bound (hdeg : MinimumDegreeThree G) (c b : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (hcb : c < b) (hb : b < 1)
    (hn : 0 < Fintype.card V) (n g : ℕ) (hg : g ≤ G.girth)
    (M : ℝ) (hM : 0 ≤ M)
    (hMass : ∀ v, ∑ i : SlowModes G c, vertexModeWeight G hdeg c hc hcouter v i ≤ M)
    (hκ : 0 ≤ collisionDecay G b (n + 1)) (hκone : collisionDecay G b (n + 1) < 1) :
    (∑ t : Fin (n + 1), if t ≠ 0 then
      ∑ v : V, returnMass G t.val v * returnMass G (n + 1 - t.val) v else 0) ≤
      (n + 1 : ℝ) * vertexWeightConstant c * M * slowMoment G c (n + 1) +
      2 * vertexWeightConstant c * returnConstant c b * slowMoment G c (n + 1) *
        collisionDecay G b (n + 1) ^ g / (1 - collisionDecay G b (n + 1)) +
      (n + 1 : ℝ) * (Fintype.card V : ℝ) * returnConstant c b ^ 2 * b ^ (n + 1) := by
  classical
  let L := n + 1
  let C := vertexWeightConstant c
  let E := returnConstant c b
  let S := slowMoment G c L
  let κ := collisionDecay G b L
  let T := collisionTimes L g
  have hC : 0 ≤ C := by
    dsimp [C, vertexWeightConstant]
    have hd : 0 < 2 * c ^ 2 - 1 := by linarith
    positivity
  have hE : 0 ≤ E := by
    dsimp [E, returnConstant]
    have hd := cutoffRadius_pos c b hcb
    have hC := remainderConstant_gt_two c b hc hcouter hcb hb
    positivity
  have hS : 0 ≤ S := slowMoment_nonneg G c L
  have hbpos := hc.trans hcb
  have hcard : (T.card : ℝ) ≤ L := by exact_mod_cast collisionTimes_card_le L g
  have hgeom := collisionTimes_geometric_sum_le L g κ hκ hκone
  have hpoint : ∀ t ∈ T, (∑ v : V, returnMass G t.val v * returnMass G (L - t.val) v) ≤
      C * M * S + C * E * S * (κ ^ t.val + κ ^ (L - t.val)) +
      (Fintype.card V : ℝ) * E ^ 2 * b ^ L := by
    intro t ht
    have hp := (Finset.mem_filter.mp ht).2.1
    have hs : 0 < L - t.val := by have := t.isLt; omega
    have hts : t.val + (L - t.val) = L := by have := t.isLt; omega
    have h := sum_returnMass_products_le G hdeg c b hc hcouter hcb hb hn M hM hMass
      t.val (L - t.val) hp hs
    rwa [hts] at h
  rw [return_collision_sum_eq_restricted G n g hg]
  calc
    _ ≤ ∑ t ∈ T, (C * M * S + C * E * S * (κ ^ t.val + κ ^ (L - t.val)) +
        (Fintype.card V : ℝ) * E ^ 2 * b ^ L) := Finset.sum_le_sum hpoint
    _ = (T.card : ℝ) * (C * M * S) + C * E * S *
        (∑ t ∈ T, (κ ^ t.val + κ ^ (L - t.val))) +
        (T.card : ℝ) * ((Fintype.card V : ℝ) * E ^ 2 * b ^ L) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [nsmul_eq_mul]
      simp only [Finset.sum_add_distrib]
      ring
    _ ≤ (L : ℝ) * (C * M * S) + C * E * S * (2 * κ ^ g / (1 - κ)) +
        (L : ℝ) * ((Fintype.card V : ℝ) * E ^ 2 * b ^ L) := by
      apply add_le_add
      · exact add_le_add
          (mul_le_mul_of_nonneg_right hcard (by positivity))
          (mul_le_mul_of_nonneg_left hgeom (by positivity))
      · exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      dsimp [L, C, E, S, κ]
      push_cast
      ring

/-- A sufficient scalar error bound for the exact simple-cycle conclusion.
This is an intermediate criterion, not the final size-threshold theorem. -/
theorem cycle_of_small_error (hdeg : MinimumDegreeThree G) (c b : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (hcb : c < b) (hb : b < 1)
    (hn : 0 < Fintype.card V) (n g : ℕ) (hL : 3 ≤ n + 1) (heven : Even (n + 1))
    (hg : g ≤ G.girth) (M : ℝ) (hM : 0 ≤ M)
    (hMass : ∀ v, ∑ i : SlowModes G c, vertexModeWeight G hdeg c hc hcouter v i ≤ M)
    (hκ : 0 ≤ collisionDecay G b (n + 1)) (hκone : collisionDecay G b (n + 1) < 1)
    (hsmall : vertexWeightConstant c * (n + 1 : ℝ) ^ 2 * M +
      2 * vertexWeightConstant c * returnConstant c b * (n + 1 : ℝ) *
        collisionDecay G b (n + 1) ^ g / (1 - collisionDecay G b (n + 1)) +
      (Fintype.card V : ℝ) * returnConstant c b ^ 2 * (n + 1 : ℝ) ^ 2 * b ^ (n + 1) +
      (2 * G.edgeFinset.card : ℝ) * (2 * b * remainderConstant c b / cutoffRadius c b) * b ^ (n + 1) < 1) :
    HasCycleLength G (n + 1) := by
  by_contra hno
  have hupper := trace_le_return_collisions_of_no_cycle G n hL hno
  have hsum := return_collision_sum_bound G hdeg c b hc hcouter hcb hb hn n g hg M hM hMass hκ hκone
  have hupper' := hupper.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hlower := even_trace_lower_bound G hdeg c b hc hcouter hcb hb (n + 1) heven
  have hS := slowMoment_ge_one G hdeg c (hcb.trans hb) hn (n + 1)
  have hbpos := hc.trans hcb
  have hη := cutoffRadius_pos c b hcb
  have hC := remainderConstant_gt_two c b hc hcouter hcb hb
  have hB : 0 ≤ (Fintype.card V : ℝ) * returnConstant c b ^ 2 * (n + 1 : ℝ) ^ 2 * b ^ (n + 1) +
      (2 * G.edgeFinset.card : ℝ) * (2 * b * remainderConstant c b / cutoffRadius c b) * b ^ (n + 1) := by
    positivity
  have hsmallS := mul_lt_mul_of_pos_right hsmall
    (by linarith : 0 < slowMoment G c (n + 1))
  have hBS := mul_le_mul_of_nonneg_left hS hB
  ring_nf at hupper' hlower hsmallS hBS
  linarith only [hupper', hlower, hsmallS, hBS]

end GirthVerification
