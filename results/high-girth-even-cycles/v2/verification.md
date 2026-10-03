# Lean verification of the high-girth even-cycle theorem

This version supplies a complete Lean proof of the exact theorem stated in
[the original preprint](../v1/manuscript.md), together with its power-of-two
corollary. It preserves the original preprint and its disclosure record.

The theorem asserts that an absolute natural number \(n_0\) exists such that
every finite simple graph on \(n\ge n_0\) vertices, with minimum degree at
least three and girth at least \(40\log\log n\), has a vertex-simple cycle
of every even natural length \(L\) in

\[
\frac{4\log(2|E|)}{\log(20/19)}\le L\le
\frac{8\log(2|E|)}{\log(20/19)}.
\]

No upper degree, connectivity, regularity, expansion or mixing assumption
is imposed. The corollary gives a cycle of length \(2^k\), with \(k\ge2\).
Neither result resolves the unrestricted Erdős–Gyárfás conjecture. The proof
establishes an absolute threshold by an eventual limiting argument; it does
not compute or optimize a numerical threshold.

## Exact statement comparison

The final declarations are
`GirthVerification.exact_even_cycle_theorem` and
`GirthVerification.exact_power_of_two_corollary` in
[Complete.lean](lean/Girth/Complete.lean). They have no unproved theorem
premise. Their literal target propositions are defined in
[Statement.lean](lean/Girth/Statement.lean).

| Mathematical requirement | Formal representation |
| --- | --- |
| Absolute size threshold | `∃ n₀ : ℕ`, preceding all graph quantifiers |
| Every finite simple graph | `∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]` |
| Size at least the threshold | `n₀ ≤ Fintype.card V` |
| Minimum degree at least three | `∀ v : V, 3 ≤ G.degree v` |
| Exact girth hypothesis | `40 * Real.log (Real.log (Fintype.card V : ℝ)) ≤ (G.girth : ℝ)` |
| Every even length | `∀ L : ℕ, Even L → InLengthInterval G L → HasCycleLength G L` |
| Exact closed interval | The two inequalities above, with `G.edgeFinset.card` as the edge count |
| Vertex-simple cycle | `∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = L` |
| Power-of-two conclusion | `∃ k : ℕ, 2 ≤ k ∧ HasCycleLength G (2 ^ k)` |

`Real.log` is the natural logarithm. The interval's left endpoint is at
least four under the nonempty graph and minimum-degree hypotheses. Thus
the natural-length formulation retains all admissible even integer lengths.
Mathlib's `Walk.IsCycle` is used in the conclusion. A weighted closed word
or a positive scalar trace alone is insufficient: the formal proof constructs
an actual `Walk.IsCycle` after controlling repeated vertices.

The audit script separately type-checks the final declarations against both
literal target propositions. This comparison was performed by the authoring
assistant; no additional independent human statement review is claimed.

## Proof implementation and changes

The formal development constructs the actual arbitrary-degree weighted
non-backtracking matrix, its reversal involution, normalized outer modes and
projectors. It proves the graph quadratic bound, outer semisimplicity,
dimension-independent frame and resolvent estimates, the real-axis analytic
bound and the Cauchy power estimate. Inner Jordan blocks are allowed.

It then proves the exact signed return expansion, vanishing below girth,
the two-cutoff mass bounds, weighted Young and finite Hölder estimates.
Finite matrix-word sums, rotation and a marked intermediate vertex justify
the collision charge, including the weights at both closing seams. Positive
words with distinct vertices are converted into actual graph cycles.

Two sufficient intermediate estimates differ from the preprint:

1. The residual power bound gives a trace error \(NK\rho^L\), where
   \(N=2|E|\), in place of the algebraic-multiplicity error
   \(N2^{-L/2}\). On the required interval, \(\rho^L\le N^{-4}\), so
   this error is at most \(KN^{-3}\).
2. Ordered collision charges give a factor \(L\), in place of \(L/2\).
   This doubles the corresponding constants without changing the final
   theorem or the fixed girth coefficient forty.

The resulting sufficient error, with the constants defined in the source,
is

\[
C_wL^2M_g+
\frac{2C_wE_1L\kappa^g}{1-\kappa}+
nE_1^2L^2\rho^L+NK\rho^L<1.
\]

The formal estimates give \(L\le320\log n\), \(\kappa\le97/100\),
and an absolute upper bound consisting of constant multiples of

\[
(\log n)^{-22/9},\qquad
(\log n)^{-1/5},\qquad
(\log n)^2n^{-3},\qquad n^{-3}.
\]

Each tends to zero. This produces the absolute threshold used in the final
graph theorem. These are proof changes with the same exact conclusion,
not a weakening of the public claim.

## Reproduction and trust

The project pins Lean `leanprover/lean4:v4.27.0` and mathlib commit
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. Its complete dependency lock is
[lake-manifest.json](lean/lake-manifest.json). See
[the project instructions](lean/README.md) for a clean build and audit.

The verification script rebuilds the library, scans project source for proof
holes, prints the axioms of every named theorem, and checks both final theorem
types. The only allowed logical foundations are `propext`, `Classical.choice`
and `Quot.sound`. The Lean kernel and the pinned toolchain are part of the
trust basis. Build and axiom evidence accompanies the release.

Formal verification does not establish exhaustive novelty, historical
priority, journal acceptance or independent human peer review. The original
preprint contains the prior-work discussion and its review limitations;
this version adds the formal proof and build evidence.

The release check passed a clean project-source rebuild and audited all 320
named project theorems. Both literal final statement type checks passed, with
no source proof holes, unexpected axioms or missing audit outputs. The public
source hashes match that build. The [audit record](verification/verification.json),
[printed axioms](verification/axioms.txt), [clean build output](verification/build.txt)
and [release validation](verification/release-validation.json) retain this evidence.
The [audit source](verification/Audit.lean) includes the final typed checks.

## Attribution and licensing

Edison Yi directs and maintains the Math Frontier campaign. OpenAI Codex
performed the substantive formalization and the proof implementation changes.
AI assistance is disclosed. This does not assert that Edison personally
derived or line-checked every proof, nor that an external human referee has
endorsed the result. The original preprint's additional contributor and
AI-assistance disclosures remain in that preserved version.

The public timestamp records disclosure and does not guarantee priority over
earlier work. No additional reuse license for the copyrightable prose or
project source is granted in this version. Lean and mathlib retain their own
upstream licenses. The mathematical statements and methods may be cited.
