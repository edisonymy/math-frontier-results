import Girth.ModeMoments
import Girth.WeightedMoments

namespace GirthVerification

theorem mixed_cardinal_power (N b : ℝ) (hN : 0 ≤ N) (t s : ℕ) :
    b ^ t * N ^ ((t : ℝ) / (t + s : ℕ)) =
      (b * N ^ (1 / (t + s : ℕ) : ℝ)) ^ t := by
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast _ t, ← Real.rpow_mul hN]
  congr 1
  ring

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem sum_unsignedReturnMain_products_le (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (M : ℝ) (hMpos : 0 ≤ M)
    (hMass : ∀ v, ∑ i : SlowModes G c, vertexModeWeight G hdeg c hc hcouter v i ≤ M)
    (t s : ℕ) (ht : 0 < t) (hs : 0 < s) :
    ∑ v : V, unsignedReturnMain G hdeg c hc hcouter t v * unsignedReturnMain G hdeg c hc hcouter s v ≤
      vertexWeightConstant c * M * slowMoment G c (t + s) := by
  have h := sum_weighted_moment_products_le
    (vertexModeWeight G hdeg c hc hcouter) (fun i : SlowModes G c => |slowValue G c i|)
    (vertexModeWeight_nonneg G hdeg c hc hcouter) (fun _ => abs_nonneg _)
    M (vertexWeightConstant c) hMass (vertexModeWeight_sum_le G hdeg c hc hcouter) hMpos t s ht hs
  simpa only [unsignedReturnMain, slowMoment, mul_comm] using h

noncomputable def collisionDecay (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℝ) (L : ℕ) : ℝ :=
  b * (2 * G.edgeFinset.card : ℝ) ^ (1 / (L : ℝ))

/-- The graph return-product estimate (18), derived from the actual
cutoff weights, weighted Young and finite Hölder. -/
theorem sum_returnMass_products_le (hdeg : MinimumDegreeThree G) (c b : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (hcb : c < b) (hb : b < 1)
    (hn : 0 < Fintype.card V) (M : ℝ) (hMpos : 0 ≤ M)
    (hMass : ∀ v, ∑ i : SlowModes G c, vertexModeWeight G hdeg c hc hcouter v i ≤ M)
    (t s : ℕ) (ht : 0 < t) (hs : 0 < s) :
    ∑ v : V, returnMass G t v * returnMass G s v ≤
      vertexWeightConstant c * M * slowMoment G c (t + s) +
      vertexWeightConstant c * returnConstant c b * slowMoment G c (t + s) *
        (collisionDecay G b (t + s) ^ t + collisionDecay G b (t + s) ^ s) +
      (Fintype.card V : ℝ) * returnConstant c b ^ 2 * b ^ (t + s) := by
  let U := unsignedReturnMain G hdeg c hc hcouter
  let C := vertexWeightConstant c
  let E := returnConstant c b
  let S := slowMoment G c (t + s)
  let N : ℝ := 2 * G.edgeFinset.card
  have hCpos : 0 ≤ C := by
    dsimp [C, vertexWeightConstant]
    have hh : 0 < 2 * c ^ 2 - 1 := by linarith
    positivity
  have hbpos := hc.trans hcb
  have hEpos : 0 ≤ E := by
    have hη := cutoffRadius_pos c b hcb
    have hC := remainderConstant_gt_two c b hc hcouter hcb hb
    dsimp [E, returnConstant]
    positivity
  have hU : ∀ k v, 0 ≤ U k v := by
    intro k v
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (pow_nonneg (abs_nonneg _) _)
      (vertexModeWeight_nonneg G hdeg c hc hcouter v i))
  have hL1 : slowMoment G c t ≤ N ^ ((s : ℝ) / (t + s : ℕ)) * S := by
    simpa [N, S, Nat.add_comm] using slowMoment_lower_le G hdeg c hc hcouter
      (hcb.trans hb) hn s t hs ht
  have hL2 : slowMoment G c s ≤ N ^ ((t : ℝ) / (t + s : ℕ)) * S :=
    slowMoment_lower_le G hdeg c hc hcouter (hcb.trans hb) hn t s ht hs
  have hmixT : (E * b ^ s) * (∑ v : V, U t v) ≤ C * E * S * collisionDecay G b (t + s) ^ s := by
    calc
      _ ≤ (E * b ^ s) * (C * slowMoment G c t) := mul_le_mul_of_nonneg_left
        (sum_unsignedReturnMain_le G hdeg c hc hcouter t) (by positivity)
      _ ≤ (E * b ^ s) * (C * (N ^ ((s : ℝ) / (t + s : ℕ)) * S)) := by gcongr
      _ = C * E * S * (b ^ s * N ^ ((s : ℝ) / (t + s : ℕ))) := by ring
      _ = _ := by
        have hpow := mixed_cardinal_power N b (by dsimp [N]; positivity) s t
        rw [Nat.add_comm s t] at hpow
        rw [hpow]
        rfl
  have hmixS : (E * b ^ t) * (∑ v : V, U s v) ≤ C * E * S * collisionDecay G b (t + s) ^ t := by
    calc
      _ ≤ (E * b ^ t) * (C * slowMoment G c s) := mul_le_mul_of_nonneg_left
        (sum_unsignedReturnMain_le G hdeg c hc hcouter s) (by positivity)
      _ ≤ (E * b ^ t) * (C * (N ^ ((t : ℝ) / (t + s : ℕ)) * S)) := by gcongr
      _ = C * E * S * (b ^ t * N ^ ((t : ℝ) / (t + s : ℕ))) := by ring
      _ = _ := by rw [mixed_cardinal_power N b (by dsimp [N]; positivity)]; rfl
  have hprod := sum_unsignedReturnMain_products_le G hdeg c hc hcouter M hMpos hMass t s ht hs
  have hpoly : ∀ v : V, (U t v + E * b ^ t) * (U s v + E * b ^ s) =
      U t v * U s v + (E * b ^ s) * U t v + (E * b ^ t) * U s v + E ^ 2 * b ^ (t + s) := by
    intro v
    rw [pow_add]
    ring
  calc
    _ ≤ ∑ v : V, (U t v + E * b ^ t) * (U s v + E * b ^ s) := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul
        (returnMass_le_unsigned_add_error G hdeg c b hc hcouter hcb hb t ht v)
        (returnMass_le_unsigned_add_error G hdeg c b hc hcouter hcb hb s hs v)
        (returnMass_nonneg G s v) (add_nonneg (hU t v) (mul_nonneg hEpos (pow_nonneg hbpos.le _)))
    _ = (∑ v : V, U t v * U s v) + (E * b ^ s) * (∑ v : V, U t v) +
        (E * b ^ t) * (∑ v : V, U s v) + (Fintype.card V : ℝ) * E ^ 2 * b ^ (t + s) := by
      simp_rw [hpoly, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [nsmul_eq_mul, mul_assoc]
      ring
    _ ≤ C * M * S + C * E * S * collisionDecay G b (t + s) ^ s +
        C * E * S * collisionDecay G b (t + s) ^ t + (Fintype.card V : ℝ) * E ^ 2 * b ^ (t + s) :=
      add_le_add (add_le_add (add_le_add hprod hmixT) hmixS) le_rfl
    _ = _ := by change _ = C * M * S + C * E * S * _ + _; ring

end GirthVerification
