import Girth.Projector

namespace GirthVerification

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def residualProjector (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) : Module.End ℂ (G.Dart → ℂ) :=
  1 - slowProjector G hdeg c hc hcouter

theorem residualProjector_apply (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (x : G.Dart → ℂ) :
    residualProjector G hdeg c hc hcouter x = x - slowProjector G hdeg c hc hcouter x := rfl

theorem residualProjector_idempotent (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    residualProjector G hdeg c hc hcouter * residualProjector G hdeg c hc hcouter =
      residualProjector G hdeg c hc hcouter := by
  have hp : slowProjector G hdeg c hc hcouter * slowProjector G hdeg c hc hcouter =
      slowProjector G hdeg c hc hcouter := slowProjector_idempotent G hdeg c hc hcouter
  unfold residualProjector
  simp only [mul_sub, sub_mul, one_mul, mul_one, hp, sub_self, sub_zero]

theorem residualProjector_commutes (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    transitionEnd G * residualProjector G hdeg c hc hcouter =
      residualProjector G hdeg c hc hcouter * transitionEnd G := by
  have hp : transitionEnd G * slowProjector G hdeg c hc hcouter =
      slowProjector G hdeg c hc hcouter * transitionEnd G := slowProjector_commutes G hdeg c hc hcouter
  simp [residualProjector, mul_sub, sub_mul, hp]

theorem slowProjector_outer_generalized_identity (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (z : outerRealEigenvalues G c)
    (n : ℕ) (x : G.Dart → ℂ) (hx : ((transitionEnd G - (z.val : ℂ) • 1) ^ n) x = 0) :
    slowProjector G hdeg c hc hcouter x = x := by
  have ht : x ∈ (transitionEnd G).genEigenspace (z.val : ℂ) ⊤ :=
    Module.End.mem_genEigenspace_top.mpr ⟨n, hx⟩
  rw [outer_genEigenspace_eq_eigenspace G hdeg z.val (outer_real_sq_gt_half G c hc hcouter z)] at ht
  exact slowProjector_outer_identity G hdeg c hc hcouter z ⟨x, ht⟩

theorem residualProjector_outer_generalized_zero (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (z : outerRealEigenvalues G c)
    (n : ℕ) (x : G.Dart → ℂ) (hx : ((transitionEnd G - (z.val : ℂ) • 1) ^ n) x = 0) :
    residualProjector G hdeg c hc hcouter x = 0 := by
  rw [residualProjector_apply, slowProjector_outer_generalized_identity G hdeg c hc hcouter z n x hx,
    sub_self]

theorem residualProjector_inner_generalized_identity (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ) (hw : ‖w‖ ≤ c)
    (n : ℕ) (x : G.Dart → ℂ) (hx : ((transitionEnd G - w • 1) ^ n) x = 0) :
    residualProjector G hdeg c hc hcouter x = x := by
  rw [residualProjector_apply, slowProjector_inner_generalized_zero G hdeg c hc hcouter w hw n x hx,
    sub_zero]

theorem residual_range_invariant (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    ∀ x ∈ (residualProjector G hdeg c hc hcouter).range,
      transitionEnd G x ∈ (residualProjector G hdeg c hc hcouter).range := by
  rintro x ⟨y, rfl⟩
  have h := congrArg (fun f : Module.End ℂ (G.Dart → ℂ) => f y)
    (residualProjector_commutes G hdeg c hc hcouter)
  exact ⟨transitionEnd G y, h.symm⟩

noncomputable def residualRestrictedEnd (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) :
    Module.End ℂ (residualProjector G hdeg c hc hcouter).range :=
  (transitionEnd G).restrict (residual_range_invariant G hdeg c hc hcouter)

/-- The actual remaining invariant subspace has all eigenvalues in the
cutoff disc. This is sufficient to define an analytic reduced resolvent
outside the disc, without assuming that the subspace is diagonalizable. -/
theorem residualRestrictedEnd_eigenvalue_norm_le (hdeg : MinimumDegreeThree G) (c : ℝ)
    (hc : 0 < c) (hcouter : 1 / 2 < c ^ 2) (w : ℂ)
    (hw : (residualRestrictedEnd G hdeg c hc hcouter).HasEigenvalue w) : ‖w‖ ≤ c := by
  by_contra hwc
  have hwc' : c < ‖w‖ := lt_of_not_ge hwc
  obtain ⟨x, hx⟩ := hw.exists_hasEigenvector
  have hxne : (x : G.Dart → ℂ) ≠ 0 := by
    intro h
    apply hx.2
    exact Subtype.ext h
  have hPx : transitionEnd G x.val = w • x.val :=
    congrArg Subtype.val hx.apply_eq_smul
  have hweigen : (transitionEnd G).HasEigenvalue w := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := x.val)
    exact ⟨Module.End.mem_eigenspace_iff.mpr hPx, hxne⟩
  obtain ⟨z, hz⟩ := outer_eigenvalue_in_real_index G hdeg c hc hcouter w hweigen hwc'
  have hshift : (transitionEnd G - (z.val : ℂ) • 1) x.val = 0 := by
    change transitionEnd G x.val - (z.val : ℂ) • x.val = 0
    rw [hz, hPx, sub_self]
  have hz0 := residualProjector_outer_generalized_zero G hdeg c hc hcouter z 1 x.val
    (by simpa using hshift)
  obtain ⟨y, hy⟩ := x.property
  have hid := congrArg (fun f : Module.End ℂ (G.Dart → ℂ) => f y)
    (residualProjector_idempotent G hdeg c hc hcouter)
  change residualProjector G hdeg c hc hcouter (residualProjector G hdeg c hc hcouter y) =
    residualProjector G hdeg c hc hcouter y at hid
  rw [hy, hz0] at hid
  exact hxne hid.symm

end GirthVerification
