import Girth.CutoffMass
import Girth.FiniteMoments

namespace GirthVerification

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def slowMoment (c : ℝ) (t : ℕ) : ℝ :=
  ∑ i : SlowModes G c, |slowValue G c i| ^ t

theorem slowMoment_nonneg (c : ℝ) (t : ℕ) : 0 ≤ slowMoment G c t := by
  exact Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg _) _)

theorem exists_slowValue_one (hdeg : MinimumDegreeThree G) (c : ℝ) (hc : c < 1)
    (hn : 0 < Fintype.card V) : ∃ i : SlowModes G c, slowValue G c i = 1 := by
  have he := transitionEnd_hasEigenvalue_one G hdeg hn
  obtain ⟨x, hx⟩ := he.exists_hasEigenvector
  have hd : 0 < Module.finrank ℂ (outerEigenspace G 1) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨x, hx.1⟩, ?_⟩
    intro hh
    exact hx.2 (congrArg Subtype.val hh)
  refine ⟨⟨⟨1, by simpa using he, by simpa using hc⟩, ⟨0, hd⟩⟩, rfl⟩

theorem slowMoment_ge_one (hdeg : MinimumDegreeThree G) (c : ℝ) (hc : c < 1)
    (hn : 0 < Fintype.card V) (t : ℕ) : 1 ≤ slowMoment G c t := by
  classical
  obtain ⟨i, hi⟩ := exists_slowValue_one G hdeg c hc hn
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun j : SlowModes G c => |slowValue G c j| ^ t)
    (fun j _ => pow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)
  simpa [hi, slowMoment] using h

theorem slowMoment_lower_le (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (hcone : c < 1)
    (hn : 0 < Fintype.card V) (t s : ℕ) (ht : 0 < t) (hs : 0 < s) :
    slowMoment G c s ≤ (2 * G.edgeFinset.card : ℝ) ^ ((t : ℝ) / (t + s : ℕ)) *
      slowMoment G c (t + s) := by
  have hL : (0 : ℝ) < (t + s : ℕ) := by exact_mod_cast (by omega : 0 < t + s)
  have hexp : (s : ℝ) / (t + s : ℕ) ≤ 1 := by
    apply (div_le_one hL).mpr
    exact_mod_cast (by omega : s ≤ t + s)
  have h := finite_lower_moment_bound (fun i : SlowModes G c => |slowValue G c i|)
    (fun _ => abs_nonneg _) t s ht hs
  calc
    _ ≤ (Fintype.card (SlowModes G c) : ℝ) ^ ((t : ℝ) / (t + s : ℕ)) *
        slowMoment G c (t + s) ^ ((s : ℝ) / (t + s : ℕ)) := h
    _ ≤ (2 * G.edgeFinset.card : ℝ) ^ ((t : ℝ) / (t + s : ℕ)) *
        slowMoment G c (t + s) := by
      apply mul_le_mul
      · apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        exact_mod_cast slowModes_card_le_darts G hdeg c hc hcouter
      · exact Real.rpow_le_self_of_one_le (slowMoment_ge_one G hdeg c hcone hn _) hexp
      · exact Real.rpow_nonneg (slowMoment_nonneg G c _) _
      · exact Real.rpow_nonneg (by positivity) _

theorem sum_unsignedReturnMain_le (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (t : ℕ) :
    ∑ v : V, unsignedReturnMain G hdeg c hc hcouter t v ≤ vertexWeightConstant c * slowMoment G c t := by
  unfold unsignedReturnMain slowMoment
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.mul_sum, mul_comm (vertexWeightConstant c)]
  exact mul_le_mul_of_nonneg_left (vertexModeWeight_sum_le G hdeg c hc hcouter i)
    (pow_nonneg (abs_nonneg _) _)

end GirthVerification
