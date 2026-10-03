import Girth.ReturnError

namespace GirthVerification

open scoped InnerProductSpace
open WithLp

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem outgoingIndicator_inner_block_bound (v : V) (x : EuclideanSpace ℂ G.Dart) :
    ‖⟪outgoingIndicator G v, x⟫_ℂ‖ ^ 2 ≤ (G.degree v : ℝ) *
      ∑ e : G.Dart, if e.fst = v then ‖x e‖ ^ 2 else 0 := by
  classical
  let y : EuclideanSpace ℂ G.Dart := toLp 2 (fun e => if e.fst = v then x e else 0)
  have hi : ⟪outgoingIndicator G v, x⟫_ℂ = ⟪outgoingIndicator G v, y⟫_ℂ := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, outgoingIndicator, y, apply_ite]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> rfl
  have hy : ‖y‖ ^ 2 = ∑ e : G.Dart, if e.fst = v then ‖x e‖ ^ 2 else 0 := by
    simp [EuclideanSpace.norm_sq_eq, y, apply_ite, ite_pow]
  rw [hi, ← outgoingIndicator_norm_sq G v, ← hy, ← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_inner_le_norm _ _)

theorem sum_indicator_inner_sq_div_excess (hdeg : MinimumDegreeThree G)
    (x : EuclideanSpace ℂ G.Dart) :
    ∑ v : V, ‖⟪outgoingIndicator G v, x⟫_ℂ‖ ^ 2 / (excessDegree G v : ℝ) ≤
      (3 / 2 : ℝ) * ‖x‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ v : V, (3 / 2 : ℝ) *
        ∑ e : G.Dart, if e.fst = v then ‖x e‖ ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro v _
      have hq := excessDegree_real_pos G hdeg v
      have hS : 0 ≤ ∑ e : G.Dart, if e.fst = v then ‖x e‖ ^ 2 else 0 := by positivity
      calc
        _ ≤ ((G.degree v : ℝ) *
            ∑ e : G.Dart, if e.fst = v then ‖x e‖ ^ 2 else 0) / (excessDegree G v : ℝ) :=
          div_le_div_of_nonneg_right (outgoingIndicator_inner_block_bound G v x) hq.le
        _ = ((G.degree v : ℝ) / (excessDegree G v : ℝ)) *
            ∑ e : G.Dart, if e.fst = v then ‖x e‖ ^ 2 else 0 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (degree_div_excessDegree_le G hdeg v) hS
    _ = (3 / 2 : ℝ) * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm, EuclideanSpace.norm_sq_eq]
      simp [eq_comm]

theorem slowVector_euclidean_norm_sq_le (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (i : SlowModes G c) :
    ‖toLp 2 (slowVector G hdeg c hc hcouter i)‖ ^ 2 ≤ c / (2 * c ^ 2 - 1) := by
  classical
  let s := eigenSign (slowValue G c i)
  let j : SignedSlowModes G c s := ⟨i, rfl⟩
  let u : EuclideanSpace ℂ (SignedSlowModes G c s) := toLp 2 (Pi.single j (1 : ℂ))
  have hu : ‖u‖ = 1 := by
    have hsq : ‖u‖ ^ 2 = 1 := by simp [u, EuclideanSpace.norm_sq_eq, Pi.single_apply, ite_pow]
    have hn := norm_nonneg u
    nlinarith
  have hfu := (signFrame G hdeg c hc hcouter s).le_opNorm u
  rw [hu, mul_one, signFrame_single] at hfu
  have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hfu
  exact hsq.trans (actual_signFrame_norm_sq_le G hdeg c hc hcouter s (eigenSign_cases _))

noncomputable def vertexWeightConstant (c : ℝ) : ℝ := 3 / (2 * (2 * c ^ 2 - 1))

/-- Total weight of one actual normalized mode over all graph vertices,
the bound (16), with no upper bound on vertex degrees. -/
theorem vertexModeWeight_sum_le (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (i : SlowModes G c) :
    ∑ v : V, vertexModeWeight G hdeg c hc hcouter v i ≤ vertexWeightConstant c := by
  have hden : 0 < 2 * c ^ 2 - 1 := by linarith
  have hvalue : c ≤ |slowValue G c i| := i.1.property.2.le
  have hvpos := hc.trans_le hvalue
  have hsum := sum_indicator_inner_sq_div_excess G hdeg
    (toLp 2 (slowVector G hdeg c hc hcouter i))
  have hnorm := slowVector_euclidean_norm_sq_le G hdeg c hc hcouter i
  calc
    _ = (∑ v : V, ‖⟪outgoingIndicator G v, toLp 2 (slowVector G hdeg c hc hcouter i)⟫_ℂ‖ ^ 2 /
        (excessDegree G v : ℝ)) / |slowValue G c i| := by
      simp only [vertexModeWeight, div_mul_eq_div_div, Finset.sum_div]
    _ ≤ ((3 / 2 : ℝ) * ‖toLp 2 (slowVector G hdeg c hc hcouter i)‖ ^ 2) /
        |slowValue G c i| := div_le_div_of_nonneg_right hsum hvpos.le
    _ ≤ ((3 / 2 : ℝ) * (c / (2 * c ^ 2 - 1))) / |slowValue G c i| := by
      gcongr
    _ ≤ ((3 / 2 : ℝ) * (c / (2 * c ^ 2 - 1))) / c :=
      div_le_div_of_nonneg_left (by positivity) hc hvalue
    _ = vertexWeightConstant c := by
      unfold vertexWeightConstant
      field_simp

end GirthVerification
