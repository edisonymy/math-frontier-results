# Complete Lean proof

This project proves the exact high-girth even-cycle theorem and its
power-of-two corollary. The declarations are
`GirthVerification.exact_even_cycle_theorem` and
`GirthVerification.exact_power_of_two_corollary` in `Girth/Complete.lean`.
The literal propositions are in `Girth/Statement.lean`.

The theorem retains arbitrary degrees and disconnected finite simple graphs.
It assumes minimum degree at least three and girth at least `40 log(log n)`
and gives every even length in the stated closed logarithmic interval.
See [the statement comparison and proof notes](../verification.md).

## Build and audit

Install the Lean/Elan toolchain manager and Python 3, then run from this directory:

```text
lake update
lake exe cache get
python scripts/check.py --clean --require-complete
```

The pinned toolchain is `leanprover/lean4:v4.27.0`. Mathlib is fixed at commit
`a3a10db0e9d66acbebf76c5e6a135066525ac900`, and all transitive dependency
revisions are retained in `lake-manifest.json`. The mathlib cache is an optional
build acceleration. No cache files or compiled proof objects are part of this
source package. A source build can be run with `lake build`.

On Windows, if `ELAN_HOME` is absent the audit script uses the normal `.elan`
directory under the current user's home directory. Set that variable to your
actual Elan location if needed.

The script checks every named project theorem's printed axiom dependencies,
rejects project proof holes and unexpected axioms, and separately type-checks
the final declarations against both exact target propositions. The trusted
foundations allowed are `propext`, `Classical.choice` and `Quot.sound`.
Reports are written to `.lake/verification/` and include source hashes and
dependency metadata. Only this project's verified `.lake/build/` tree is
removed by `--clean`; the dependency checkout is retained.

The public package's accompanying verification evidence records the actual
release check. Rerunning the script provides a fresh local audit. This formal
proof does not claim a computable optimized size threshold, exhaustive novelty,
independent human peer review or a solution of the unrestricted conjecture.

Edison Yi directs and maintains the campaign. OpenAI Codex performed this
formalization and proof implementation; AI assistance is disclosed. No
additional reuse license is granted for this project's source in this version.
