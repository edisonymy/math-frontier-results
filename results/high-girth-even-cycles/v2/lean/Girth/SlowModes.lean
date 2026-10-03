import Girth.SpectralData
import Mathlib.LinearAlgebra.Dimension.Finite

namespace GirthVerification

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def SlowModes (c : ℝ) : Type :=
  Σ z : outerRealEigenvalues G c, Fin (Module.finrank ℂ (outerEigenspace G z.val))

noncomputable instance (c : ℝ) : Fintype (SlowModes G c) := by
  classical
  unfold SlowModes
  infer_instance

noncomputable instance (c : ℝ) : DecidableEq (SlowModes G c) := Classical.decEq _

def slowValue (c : ℝ) (i : SlowModes G c) : ℝ := i.1.val

noncomputable def slowVector (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (i : SlowModes G c) : G.Dart → ℂ :=
  (normalizedOuterBasis G hdeg c hc hcouter i.1 i.2).val

theorem slowVector_eigen (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (i : SlowModes G c) :
    (complexTransition G).mulVec (slowVector G hdeg c hc hcouter i) =
      (slowValue G c i : ℂ) • slowVector G hdeg c hc hcouter i :=
  outerEigenspace_eigen G i.1.val (normalizedOuterBasis G hdeg c hc hcouter i.1 i.2)

theorem slowVector_pairing (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (i j : SlowModes G c) :
    reversalPairing G (slowVector G hdeg c hc hcouter i) (slowVector G hdeg c hc hcouter j) =
      (eigenSign (slowValue G c i) : ℂ) * if i = j then 1 else 0 := by
  classical
  obtain ⟨zi, ii⟩ := i
  obtain ⟨zj, jj⟩ := j
  by_cases h : zi = zj
  · subst zj
    have heq : (Sigma.mk zi ii : SlowModes G c) = Sigma.mk zi jj ↔ ii = jj := by
      exact (Sigma.mk.inj_iff).trans (by simp)
    simpa [slowVector, slowValue, heq] using normalizedOuterBasis_pairing G hdeg c hc hcouter zi ii jj
  · have hval : zi.val ≠ zj.val := fun he => h (Subtype.ext he)
    have hij : (Sigma.mk zi ii : SlowModes G c) ≠ Sigma.mk zj jj :=
      fun he => h (congrArg Sigma.fst he)
    have hp := distinct_real_eigenvectors_reversal_orthogonal G
      (slowVector G hdeg c hc hcouter ⟨zi, ii⟩) (slowVector G hdeg c hc hcouter ⟨zj, jj⟩)
      zi.val zj.val hval (slowVector_eigen G hdeg c hc hcouter ⟨zi, ii⟩)
      (slowVector_eigen G hdeg c hc hcouter ⟨zj, jj⟩)
    simpa [hij] using hp

theorem slowValue_abs_le_one (hdeg : MinimumDegreeThree G) (c : ℝ) (i : SlowModes G c) :
    |slowValue G c i| ≤ 1 := by
  have h := hasEigenvalue_normSq_le_one G hdeg (i.1.val : ℂ) i.1.property.1
  simp only [Complex.normSq_ofReal, ← sq] at h
  apply (sq_le_sq₀ (abs_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)).mp
  simpa [slowValue, sq_abs] using h

theorem reversalPairing_sum_right {ι : Type*} (x : G.Dart → ℂ) (s : Finset ι)
    (f : ι → (G.Dart → ℂ)) :
    reversalPairing G x (∑ i ∈ s, f i) = ∑ i ∈ s, reversalPairing G x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reversalPairing]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, reversalPairing_add_right, ih]

theorem slowVector_linearIndependent (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    LinearIndependent ℂ (slowVector G hdeg c hc hcouter) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have hp := congrArg (reversalPairing G (slowVector G hdeg c hc hcouter i)) ha
  rw [reversalPairing_sum_right] at hp
  simp_rw [reversalPairing_smul_right, slowVector_pairing] at hp
  have hsne : (eigenSign (slowValue G c i) : ℂ) ≠ 0 := by
    rcases eigenSign_cases (slowValue G c i) with h | h <;> rw [h] <;> norm_num
  have he : a i * (eigenSign (slowValue G c i) : ℂ) = 0 := by
    simpa [reversalPairing, mul_ite, eq_comm] using hp
  exact (mul_eq_zero.mp he).resolve_right hsne

/-- Counting multiplicity through actual eigenspace dimensions, the number
of slow modes never exceeds the directed-edge count. -/
theorem slowModes_card_le_darts (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    Fintype.card (SlowModes G c) ≤ 2 * G.edgeFinset.card := by
  have h := (slowVector_linearIndependent G hdeg c hc hcouter).fintype_card_le_finrank
  simpa only [Module.finrank_pi, Module.finrank_self, mul_one,
    G.dart_card_eq_twice_card_edges] using h

end GirthVerification
