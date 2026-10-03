import Girth.Statement
import Mathlib.Combinatorics.SimpleGraph.Walks.Subwalks

namespace GirthVerification

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- Backtracking is forbidden at internal positions only. -/
def InternallyNonBacktracking (p : G.Walk u v) : Prop :=
  ∀ i : ℕ, i + 2 ≤ p.length → p.getVert i ≠ p.getVert (i + 2)

theorem internallyNonBacktracking_girth_le {u : V} (p : G.Walk u u)
    (hp : InternallyNonBacktracking p) (hlen : 0 < p.length) : G.girth ≤ p.length := by
  classical
  let repeated : ℕ → Prop := fun d => ∃ i j : ℕ,
    i < j ∧ j ≤ p.length ∧ p.getVert i = p.getVert j ∧ j - i = d
  have hex : ∃ d, repeated d :=
    ⟨p.length, 0, p.length, hlen, le_rfl, by simp, by simp⟩
  obtain ⟨i, j, hij, hj, heq, hd⟩ := Nat.find_spec hex
  have hdpos : 0 < Nat.find hex := by omega
  let q := (p.drop i).take (j - i)
  have hend : (p.drop i).getVert (j - i) = p.getVert i := by
    rw [SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij.le]
    exact heq.symm
  let r : G.Walk (p.getVert i) (p.getVert i) := q.copy rfl hend
  have hrlen : r.length = j - i := by
    simp only [r, q, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length,
      SimpleGraph.Walk.drop_length]
    exact Nat.min_eq_left (by omega)
  have hrvert : ∀ k ≤ r.length, r.getVert k = p.getVert (i + k) := by
    intro k hk
    simp only [r, q, SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.take_getVert,
      SimpleGraph.Walk.drop_getVert]
    rw [Nat.min_eq_right (by omega)]
  have hrnb : InternallyNonBacktracking r := by
    intro k hk
    rw [hrvert k (by omega), hrvert (k + 2) hk]
    have hh := hp (i + k) (by omega)
    simpa [Nat.add_assoc] using hh
  have hrpos : 0 < r.length := by omega
  have hrnil : ¬ r.Nil := by
    intro hn
    have : r.length = 0 := by simp [hn.eq_nil]
    omega
  have htail : r.tail.IsPath := by
    apply (SimpleGraph.Walk.IsPath.getVert_injOn_iff r.tail).mp
    intro a ha b hb hab
    simp only [Set.mem_setOf_eq] at ha hb
    have htailLen := SimpleGraph.Walk.length_tail_add_one hrnil
    have he : p.getVert (i + (a + 1)) = p.getVert (i + (b + 1)) := by
      rw [SimpleGraph.Walk.getVert_tail, SimpleGraph.Walk.getVert_tail,
        hrvert (a + 1) (by omega), hrvert (b + 1) (by omega)] at hab
      exact hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hablt | hbaglt
    · have hh : repeated ((i + (b + 1)) - (i + (a + 1))) :=
        ⟨i + (a + 1), i + (b + 1), by omega, by omega, he, rfl⟩
      have hmin := Nat.find_min' hex hh
      omega
    · have hh : repeated ((i + (a + 1)) - (i + (b + 1))) :=
        ⟨i + (b + 1), i + (a + 1), by omega, by omega, he.symm, rfl⟩
      have hmin := Nat.find_min' hex hh
      omega
  have hcycle : r.IsCycle := by
    rw [← r.cons_tail_eq hrnil]
    apply (SimpleGraph.Walk.cons_isCycle_iff r.tail (r.adj_snd hrnil)).mpr
    constructor
    · exact htail
    · intro hedge
      have he : p.getVert i = r.tail.snd := htail.eq_snd_of_mem_edges (by
        simpa only [Sym2.eq_swap] using hedge)
      have hqpos : 0 < r.tail.length := by
        have hh : 0 < r.tail.edges.length := by
          have hn := List.ne_nil_of_mem hedge
          have hh : r.tail.edges.length ≠ 0 := fun hz => hn (List.length_eq_zero_iff.mp hz)
          omega
        simpa only [SimpleGraph.Walk.length_edges] using hh
      have htailLen := SimpleGraph.Walk.length_tail_add_one hrnil
      have hnb := hrnb 0 (by omega)
      apply hnb
      simpa [SimpleGraph.Walk.snd, SimpleGraph.Walk.getVert_tail] using he
  exact (G.girth_le_length hcycle).trans (by omega)

end GirthVerification
