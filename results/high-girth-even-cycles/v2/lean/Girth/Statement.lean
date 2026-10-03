import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The exact graph target of high-girth-even-cycles-v1. These are definitions,
not assertions that the main theorem has been proved. `Walk.IsCycle` is
mathlib's vertex-simple cycle predicate, not a closed-walk substitute.
-/

namespace GirthVerification

universe u

variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def HasCycleLength (L : ℕ) : Prop :=
  ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = L

def MinimumDegreeThree : Prop := ∀ v : V, 3 ≤ G.degree v

def HighGirth : Prop :=
  40 * Real.log (Real.log (Fintype.card V : ℝ)) ≤ (G.girth : ℝ)

def InLengthInterval (L : ℕ) : Prop :=
  4 * Real.log (2 * G.edgeFinset.card : ℝ) / Real.log (20 / 19 : ℝ) ≤ (L : ℝ) ∧
  (L : ℝ) ≤ 8 * Real.log (2 * G.edgeFinset.card : ℝ) / Real.log (20 / 19 : ℝ)

def HasAllEvenLengths : Prop :=
  ∀ L : ℕ, Even L → InLengthInterval G L → HasCycleLength G L

def HasPowerOfTwoCycle : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ HasCycleLength G (2 ^ k)

/-- This proposition states the full target, with no degree upper bound,
connectivity, regularity, expansion, or hidden spectral assumption. -/
def ExactEvenCycleTheorem : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V → MinimumDegreeThree G → HighGirth G → HasAllEvenLengths G

def ExactPowerOfTwoCorollary : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V → MinimumDegreeThree G → HighGirth G → HasPowerOfTwoCycle G

end GirthVerification
