import Girth.NonBacktracking
import Girth.NonBacktrackingWalk

namespace GirthVerification

variable {V : Type*} {G : SimpleGraph V}

theorem internallyNonBacktracking_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
    (hp : InternallyNonBacktracking p) (hfirst : u ≠ p.getVert 1) :
    InternallyNonBacktracking (p.cons h) := by
  intro i hi
  cases i with
  | zero => simpa [SimpleGraph.Walk.getVert_cons] using hfirst
  | succ i =>
    have hh := hp i (by simp only [SimpleGraph.Walk.length_cons] at hi; omega)
    simpa [SimpleGraph.Walk.getVert_cons, Nat.add_assoc] using hh

theorem nonBacktracking_fst_ne_snd (e f : G.Dart) (h : NonBacktracking G e f) :
    e.fst ≠ f.snd := by
  intro he
  apply h.2
  apply SimpleGraph.Dart.ext
  exact Prod.ext h.1.symm he.symm

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem transition_pos_nonBacktracking (e f : G.Dart) (h : 0 < transition G e f) :
    NonBacktracking G e f := by
  classical
  by_contra hn
  simp [transition, hn] at h

/-- A positive matrix entry produces an actual graph walk with the named
initial dart and no internal backtrack. -/
theorem transition_pow_pos_walk (n : ℕ) (e f : G.Dart)
    (h : 0 < (transition G ^ n) e f) :
    ∃ p : G.Walk e.fst f.snd,
      p.length = n + 1 ∧ InternallyNonBacktracking p ∧ p.getVert 1 = e.snd := by
  classical
  induction n generalizing e f with
  | zero =>
    have hef : e = f := by
      by_contra hn
      simp [Matrix.one_apply, hn] at h
    subst f
    refine ⟨e.adj.toWalk, rfl, ?_, rfl⟩
    intro i hi
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hi
    omega
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply] at h
    have hex : ∃ g : G.Dart, 0 < transition G e g * (transition G ^ n) g f := by
      by_contra hn
      push_neg at hn
      have hle := Finset.sum_nonpos (s := Finset.univ) (fun g _ => hn g)
      linarith
    obtain ⟨g, hg⟩ := hex
    have hen := transition_nonneg G e g
    have hfn := Matrix.pow_apply_nonneg (transition_nonneg G) n g f
    have heg : 0 < transition G e g := by nlinarith
    have hgf : 0 < (transition G ^ n) g f := by nlinarith
    have hnb := transition_pos_nonBacktracking G e g heg
    obtain ⟨q, hq, hqnb, hqfirst⟩ := ih g f hgf
    let q' : G.Walk e.snd f.snd := q.copy hnb.1.symm rfl
    have hq'nb : InternallyNonBacktracking q' := by
      intro i hi
      simpa [q', SimpleGraph.Walk.getVert_copy] using hqnb i (by simpa [q'] using hi)
    have hq'first : q'.getVert 1 = g.snd := by simpa [q'] using hqfirst
    refine ⟨q'.cons e.adj, ?_, internallyNonBacktracking_cons e.adj q' hq'nb ?_, ?_⟩
    · simp [q', hq, Nat.add_assoc]
    · rw [hq'first]
      exact nonBacktracking_fst_ne_snd e g hnb
    · simp [SimpleGraph.Walk.getVert_cons]

theorem transition_pow_return_eq_zero_below_girth (n : ℕ) (e f : G.Dart)
    (hclose : e.fst = f.snd) (hsmall : n + 1 < G.girth) :
    (transition G ^ n) e f = 0 := by
  have hn := Matrix.pow_apply_nonneg (transition_nonneg G) n e f
  apply le_antisymm _ hn
  by_contra hp
  have hh : 0 < (transition G ^ n) e f := lt_of_not_ge hp
  obtain ⟨p, hlen, hnb, _⟩ := transition_pow_pos_walk G n e f hh
  let q : G.Walk e.fst e.fst := p.copy rfl hclose.symm
  have hqnb : InternallyNonBacktracking q := by
    intro i hi
    simpa [q] using hnb i (by simpa [q] using hi)
  have hg := internallyNonBacktracking_girth_le q hqnb (by simp [q, hlen])
  simp only [q, SimpleGraph.Walk.length_copy, hlen] at hg
  omega

end GirthVerification
