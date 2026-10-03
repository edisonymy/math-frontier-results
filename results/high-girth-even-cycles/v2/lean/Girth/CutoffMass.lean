import Girth.VertexWeightBound

namespace GirthVerification

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def unsignedReturnMain (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (t : ℕ) (v : V) : ℝ :=
  ∑ i : SlowModes G c, |slowValue G c i| ^ t * vertexModeWeight G hdeg c hc hcouter v i

theorem signedReturnMain_le_unsigned (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (t : ℕ) (v : V) :
    signedReturnMain G hdeg c hc hcouter t v ≤ unsignedReturnMain G hdeg c hc hcouter t v := by
  apply Finset.sum_le_sum
  intro i _
  have hs : eigenSign (slowValue G c i) ^ t ≤ 1 := by
    rcases eigenSign_cases (slowValue G c i) with hs | hs
    · simp [hs]
    · rw [hs]
      have hh : |(-1 : ℝ) ^ t| = 1 := by simp [abs_pow]
      exact (le_abs_self _).trans_eq hh
  have hw := vertexModeWeight_nonneg G hdeg c hc hcouter v i
  calc
    _ = eigenSign (slowValue G c i) ^ t *
        (|slowValue G c i| ^ t * vertexModeWeight G hdeg c hc hcouter v i) := by ring
    _ ≤ 1 * (|slowValue G c i| ^ t * vertexModeWeight G hdeg c hc hcouter v i) := by gcongr
    _ = _ := one_mul _

theorem signedReturnMain_even (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (t : ℕ) (heven : Even t) (v : V) :
    signedReturnMain G hdeg c hc hcouter t v = unsignedReturnMain G hdeg c hc hcouter t v := by
  apply Finset.sum_congr rfl
  intro i _
  rcases eigenSign_cases (slowValue G c i) with hs | hs <;> simp [hs, heven.neg_one_pow]

theorem returnMass_le_unsigned_add_error (hdeg : MinimumDegreeThree G) (c b : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (hcb : c < b) (hb : b < 1)
    (t : ℕ) (ht : 1 ≤ t) (v : V) :
    returnMass G t v ≤ unsignedReturnMain G hdeg c hc hcouter t v + returnConstant c b * b ^ t := by
  rw [returnMass_eq_main_add_error G hdeg c hc hcouter t ht v]
  exact add_le_add (signedReturnMain_le_unsigned G hdeg c hc hcouter t v)
    ((le_abs_self _).trans (returnError_abs_bound G hdeg c b hc hcouter hcb hb t ht v))

def lowerCutoffMode (c r : ℝ) (hcr : c < r) (i : SlowModes G r) : SlowModes G c :=
  ⟨⟨i.1.val, i.1.property.1, hcr.trans i.1.property.2⟩, i.2⟩

theorem lowerCutoffMode_injective (c r : ℝ) (hcr : c < r) :
    Function.Injective (lowerCutoffMode G c r hcr) := by
  intro i j h
  have hz : i.1 = j.1 := Subtype.ext (congrArg (fun k : SlowModes G c => k.1.val) h)
  obtain ⟨zi, ki⟩ := i
  obtain ⟨zj, kj⟩ := j
  simp only at hz
  subst zj
  have hk : ki = kj := Fin.ext (congrArg (fun k : SlowModes G c => k.2.val) h)
  rw [hk]

theorem lowerCutoffMode_weight (hdeg : MinimumDegreeThree G) (c r : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (hr : 0 < r) (hrouter : 1 / 2 < r ^ 2)
    (hcr : c < r) (v : V) (i : SlowModes G r) :
    vertexModeWeight G hdeg c hc hcouter v (lowerCutoffMode G c r hcr i) =
      vertexModeWeight G hdeg r hr hrouter v i := rfl

theorem unsignedReturnMain_cutoff_mono (hdeg : MinimumDegreeThree G) (c r : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (hr : 0 < r) (hrouter : 1 / 2 < r ^ 2)
    (hcr : c < r) (t : ℕ) (v : V) :
    unsignedReturnMain G hdeg r hr hrouter t v ≤ unsignedReturnMain G hdeg c hc hcouter t v := by
  classical
  let f := lowerCutoffMode G c r hcr
  let W := fun i : SlowModes G c =>
    |slowValue G c i| ^ t * vertexModeWeight G hdeg c hc hcouter v i
  have hi := lowerCutoffMode_injective G c r hcr
  calc
    _ = ∑ i ∈ Finset.univ.image f, W i := by
      rw [Finset.sum_image (fun a _ b _ hab => hi hab)]
      rfl
    _ ≤ ∑ i : SlowModes G c, W i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => by
        exact mul_nonneg (pow_nonneg (abs_nonneg _) _) (vertexModeWeight_nonneg G hdeg c hc hcouter v i))
    _ = _ := rfl

/-- Vanishing at an even time below girth controls the total mass of the
actual modes above the separated higher cutoff, as in (15). -/
theorem higherCutoff_vertex_mass_le (hdeg : MinimumDegreeThree G) (c b r : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (hr : 0 < r) (hrouter : 1 / 2 < r ^ 2)
    (hcb : c < b) (hb : b < 1) (hcr : c < r)
    (t : ℕ) (ht : 1 ≤ t) (heven : Even t) (hg : t < G.girth) (v : V) :
    ∑ i : SlowModes G r, vertexModeWeight G hdeg r hr hrouter v i ≤
      returnConstant c b * (b / r) ^ t := by
  have hzero := returnMass_eq_zero_below_girth G t ht hg v
  have hexp := returnMass_eq_main_add_error G hdeg c hc hcouter t ht v
  rw [hzero, signedReturnMain_even G hdeg c hc hcouter t heven v] at hexp
  have herror := returnError_abs_bound G hdeg c b hc hcouter hcb hb t ht v
  have hmain : unsignedReturnMain G hdeg c hc hcouter t v ≤ returnConstant c b * b ^ t := by
    have hh := neg_le_abs (returnError G hdeg c hc hcouter t v)
    linarith
  have hm : r ^ t * (∑ i : SlowModes G r, vertexModeWeight G hdeg r hr hrouter v i) ≤
      returnConstant c b * b ^ t := by
    calc
      _ ≤ unsignedReturnMain G hdeg r hr hrouter t v := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hr.le i.1.property.2.le t) (vertexModeWeight_nonneg G hdeg r hr hrouter v i)
      _ ≤ unsignedReturnMain G hdeg c hc hcouter t v :=
        unsignedReturnMain_cutoff_mono G hdeg c r hc hcouter hr hrouter hcr t v
      _ ≤ _ := hmain
  have hrpow := pow_pos hr t
  calc
    _ ≤ (returnConstant c b * b ^ t) / r ^ t := (le_div_iff₀ hrpow).mpr (by simpa [mul_comm] using hm)
    _ = _ := by rw [div_pow]; ring

end GirthVerification
