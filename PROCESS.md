# Releasing a mathematical result

## One owner, one release

The authoring principal prepares the manuscript and chooses its exact claim.
The other principal contributes complementary mathematical review when available;
existing substantive Pro audits count as evidence and should be read and reused.
An unavailable reviewer does not prevent a complete, honestly labelled preprint.
The maintainer publishes the selected files and records the actual public release.

Use this process at an existing research checkpoint. There is no publication
timer, routine reviewer fleet or repeated status checking.

## Minimal sequence

1. **Prepare a complete note.** Include the exact theorem and hypotheses, proof,
   definitions, closest prior results, what is new or not yet verified, explicit
   nonclaims, contributors, AI assistance and licensing. Include supporting code
   only when the argument relies on it. A large-girth result is not an unrestricted
   conjecture resolution. An abstract or a placeholder is not a theorem release.
2. **Make one mathematical decision.** The responsible principal names the version,
   explains its scope and review status, and recommends release or lists a concrete
   defect to fix. Reuse existing review; seek another audit only for a substantive
   unresolved mathematical issue. Publication as an unrefereed preprint is distinct
   from proof acceptance or formal verification.
3. **Select the public files.** Export only that note and its necessary sources,
   references and reproducibility files into a fresh version directory. Use public
   citations, never internal evidence paths. Check attribution and permission to
   disclose included material. Run `python tools/check_publication.py` once after
   staging the selected files. Inspect the exact diff before pushing.
4. **Publish that version.** Commit it, create an annotated `<result>-v1` tag and
   a GitHub Release. Include the statement, limitations, review status and full
   proof/source in the release. Record GitHub's returned publication time, tag,
   commit and URL; never substitute a local file or commit date for public disclosure.
5. **Keep the record.** Corrections use `v2`, `v3`, etc., with a concise description
   of changed claims. Do not overwrite or retag a published theorem version.
   Append a correction/withdrawal notice and cross-link the versions. Maintain a
   short result index; do not delete an inconvenient earlier version.

## Durable evidence and citations

Enable GitHub's release immutability when the repository/account supports it.
It protects released assets and their associated tags after publication:
[GitHub documentation](https://docs.github.com/en/code-security/concepts/supply-chain-security/immutable-releases).
Until verified enabled, append-only release handling is a maintainer policy,
not a platform guarantee.

A Zenodo deposit with a version DOI is a useful additional archive. Set it up
when an authenticated archive route is available; do not delay an otherwise
ready public manuscript solely for DOI setup. GitHub integration can archive a
release after its repository is enabled:
[Zenodo documentation](https://help.zenodo.org/docs/github/).
Record a DOI only after the deposit is actually published.

Claims of novelty must identify the closest known literature and limitations of
the search. Public timestamps support a disclosure record; they do not replace
literature review or mathematical proof.

## Release notes

Use a short body: title and version; exact scope; review status; contributors and
AI assistance; links to the complete proof and sources; changes from any previous
version. Mark later-discovered defects visibly. Do not describe a scaffold or a
process release as establishing priority for a theorem.
