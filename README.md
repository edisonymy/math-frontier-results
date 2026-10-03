# Math Frontier — public research notes

Selected mathematical manuscripts, proofs and reproducibility material from
Math Frontier, maintained by [edisonymy](https://github.com/edisonymy).

This repository provides dated public versions that other researchers can
inspect and cite. A publication date records disclosure; it does not by itself
establish novelty, correctness or precedence over earlier work.

## Results

| Result | Version and status | Complete proof |
| --- | --- | --- |
| Exact even cycle lengths in high-girth graphs of minimum degree three | [v1 — unrefereed, AI-assisted preprint](https://github.com/edisonymy/math-frontier-results/releases/tag/high-girth-even-cycles-v1) | [Manuscript](results/high-girth-even-cycles/v1/manuscript.md) |
| Exact even cycle lengths and power-of-two corollary | [v2 — Lean kernel-checked proof](https://github.com/edisonymy/math-frontier-results/releases/tag/high-girth-even-cycles-v2) | [Verification, exact statements and source](results/high-girth-even-cycles/v2/verification.md) |

The first result applies to sufficiently large finite simple graphs of minimum
degree at least three and girth at least $40\log\log n$. It guarantees every
even cycle length in a specified interval proportional to $\log(2|E|)$, without
regularity or expansion assumptions. See the manuscript for exact constants,
attribution, prior work and review limitations. This repository does not announce
a solution of the unrestricted Erdős–Gyárfás conjecture.

Published notes will live under `results/<name>/v1/`, with subsequent versions in
new directories. Cite a particular release and version rather than the changing
default branch. Corrections and withdrawals will remain linked from the result.

## Reading and contributing

- Read the note's statement, hypotheses, proof, references and review status.
- Report a concrete mathematical error or missing attribution through an issue.
- See [the release process](PROCESS.md) for versioning, review and corrections.
- See [the result template](templates/RESULT.md) for the required public context.

The repository contains selected public material. It is not a mirror of the
campaign's working records. AI assistance and human/editorial contributions are
disclosed separately for each manuscript; maintenance is not an authorship claim.

Licensing is stated for each released work. No blanket license has been selected
for manuscripts that are not yet released.
