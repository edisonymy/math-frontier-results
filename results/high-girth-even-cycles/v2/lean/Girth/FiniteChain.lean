import Girth.TransitionWalk
import Girth.CyclicWords

namespace GirthVerification

variable {V : Type*} {G : SimpleGraph V}

def walkOfFiniteChain : (n : ℕ) → (w : Fin (n + 1) → V) →
    (∀ k : Fin n, G.Adj (w k.castSucc) (w k.succ)) → G.Walk (w 0) (w (Fin.last n))
  | 0, w, _ => .nil
  | n + 1, w, h => .cons (h 0) (walkOfFiniteChain n (Fin.tail w) (fun k => h k.succ))

theorem walkOfFiniteChain_length (n : ℕ) (w : Fin (n + 1) → V)
    (h : ∀ k : Fin n, G.Adj (w k.castSucc) (w k.succ)) :
    (walkOfFiniteChain n w h).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [walkOfFiniteChain, ih]

theorem walkOfFiniteChain_getVert (n : ℕ) (w : Fin (n + 1) → V)
    (h : ∀ k : Fin n, G.Adj (w k.castSucc) (w k.succ)) (i : ℕ) (hi : i ≤ n) :
    (walkOfFiniteChain n w h).getVert i = w ⟨i, by omega⟩ := by
  induction n generalizing i with
  | zero =>
    have hi0 : i = 0 := by omega
    subst i
    rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [walkOfFiniteChain, SimpleGraph.Walk.getVert_cons, Nat.succ_ne_zero, ↓reduceIte,
        Nat.add_sub_cancel]
      exact ih (Fin.tail w) (fun k => h k.succ) i (by omega)

theorem isCycle_of_getVert_injOn_tail {u : V} (p : G.Walk u u) (hlen : 3 ≤ p.length)
    (hinj : Set.InjOn p.getVert {i : ℕ | 1 ≤ i ∧ i ≤ p.length}) : p.IsCycle := by
  have hpnon : ¬ p.Nil := by
    intro hp
    have hh : p.length = 0 := by simp [hp.eq_nil]
    omega
  have htailLen := SimpleGraph.Walk.length_tail_add_one hpnon
  have htail : p.tail.IsPath := by
    apply (SimpleGraph.Walk.IsPath.getVert_injOn_iff p.tail).mp
    intro i hi j hj he
    simp only [Set.mem_setOf_eq] at hi hj
    rw [SimpleGraph.Walk.getVert_tail, SimpleGraph.Walk.getVert_tail] at he
    have hh := hinj (by constructor <;> omega) (by constructor <;> omega) he
    omega
  rw [← p.cons_tail_eq hpnon]
  apply (SimpleGraph.Walk.cons_isCycle_iff p.tail (p.adj_snd hpnon)).mpr
  refine ⟨htail, ?_⟩
  intro hedge
  have he : u = p.tail.snd := htail.eq_snd_of_mem_edges (by simpa only [Sym2.eq_swap] using hedge)
  have he' : p.getVert 2 = p.getVert p.length := by
    simpa [SimpleGraph.Walk.snd, SimpleGraph.Walk.getVert_tail] using he.symm
  have hh := hinj (by constructor <;> omega) (by constructor <;> omega) he'
  omega

theorem closed_vertices_at {α : Type*} (n : ℕ) (w : Fin (n + 1) → α) (k : Fin (n + 2)) :
    Fin.snoc (α := fun _ : Fin (n + 2) => α) w (w 0) k = w (Fin.ofNat (n + 1) k.val) := by
  refine Fin.lastCases ?_ (fun i => ?_) k
  · rw [Fin.snoc_last]
    congr 1
    apply Fin.ext
    simp
  · simp [Fin.snoc_castSucc]

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem positive_simple_word_has_cycle (n : ℕ) (hL : 3 ≤ n + 1)
    (w : Fin (n + 1) → G.Dart) (hp : 0 < matrixCycleProduct (transition G) n w)
    (hinj : Function.Injective (fun k => (w k).fst)) : HasCycleLength G (n + 1) := by
  classical
  have hprod : 0 < ∏ k : Fin (n + 1), transition G (w k) (w (k + 1)) := by
    rwa [matrixCycleProduct_eq_prod] at hp
  have hnb : ∀ k : Fin (n + 1), NonBacktracking G (w k) (w (k + 1)) := by
    intro k
    apply transition_pos_nonBacktracking G
    have hn := transition_nonneg G (w k) (w (k + 1))
    have hne : transition G (w k) (w (k + 1)) ≠ 0 := by
      intro hz
      have hh := Finset.prod_eq_zero (s := Finset.univ)
        (f := fun j : Fin (n + 1) => transition G (w j) (w (j + 1))) (Finset.mem_univ k) hz
      rw [hh] at hprod
      exact lt_irrefl _ hprod
    exact lt_of_le_of_ne hn hne.symm
  let W : Fin (n + 1) → V := fun k => (w k).fst
  let verts : Fin (n + 2) → V := Fin.snoc (α := fun _ : Fin (n + 2) => V) W (W 0)
  have hadj : ∀ k : Fin (n + 1), G.Adj (verts k.castSucc) (verts k.succ) := by
    intro k
    change G.Adj (Fin.snoc (α := fun _ : Fin (n + 2) => V) W (W 0) k.castSucc)
      (Fin.snoc (α := fun _ : Fin (n + 2) => V) W (W 0) k.succ)
    rw [Fin.snoc_castSucc, snoc_succ_eq_tail_snoc, snoc_tail_eq_cyclic_next]
    change G.Adj (w k).fst (w (k + 1)).fst
    rw [← (hnb k).1]
    exact (w k).adj
  let q := walkOfFiniteChain (n + 1) verts hadj
  let p : G.Walk (W 0) (W 0) := q.copy (by simp [verts]) (by simp [verts])
  have hplen : p.length = n + 1 := by simp [p, q, walkOfFiniteChain_length]
  have hpvert : ∀ k ≤ n + 1, p.getVert k = W (Fin.ofNat (n + 1) k) := by
    intro k hk
    rw [SimpleGraph.Walk.getVert_copy]
    change q.getVert k = _
    rw [walkOfFiniteChain_getVert (n + 1) verts hadj k hk]
    exact closed_vertices_at n W _
  have hcycle : p.IsCycle := by
    apply isCycle_of_getVert_injOn_tail p (by omega)
    intro i hi j hj heq
    simp only [Set.mem_setOf_eq] at hi hj
    rw [hpvert i (by omega), hpvert j (by omega)] at heq
    have hindex := hinj heq
    have hval := congrArg Fin.val hindex
    change i % (n + 1) = j % (n + 1) at hval
    by_cases hiend : i = n + 1
    · by_cases hjend : j = n + 1
      · omega
      · subst i
        rw [Nat.mod_self, Nat.mod_eq_of_lt (by omega : j < n + 1)] at hval
        omega
    · by_cases hjend : j = n + 1
      · subst j
        rw [Nat.mod_eq_of_lt (by omega : i < n + 1), Nat.mod_self] at hval
        omega
      · rw [Nat.mod_eq_of_lt (by omega : i < n + 1), Nat.mod_eq_of_lt (by omega : j < n + 1)] at hval
        exact hval
  exact ⟨W 0, p, hcycle, hplen⟩

end GirthVerification
