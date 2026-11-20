# STOC formalization issues

This repository records reproducible investigations of statements in STOC
formalizations. A claim of disproof is recorded as verified here only after
its negation compiles against the exact published statement and pinned
dependencies. A formal counterexample and a claim about the corresponding
paper are separate conclusions.

## Case index

| Submission | Statement | Finding | Evidence |
| --- | --- | --- | --- |
| 173 | Lemma D.17 | The published Lean statement is false for `n = m = 0`; the disproof was accepted by Prove2Me. | [Verification](VERIFICATION.md), [proof](DisproofD17.lean), [type check](StatementMatch.lean), [submission record](SUBMISSION_DRAFT.md) |

Other audit observations have not yet been checked or cataloged in this
repository. Add each one here with its source, exact formal statement,
environment, and verification status as the investigation proceeds.

## Lean layout

The repository currently has one Lake project at its root. Its
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin the environment
for submission 173. Run `lake build StatementMatch` from this directory to
check the local disproof and its match to the published declaration.

Cases that use the same Lean and mathlib versions can be added as separate
modules in this project. If another case needs a different toolchain or
dependency revision, put its own Lake project in a subdirectory and run Lake
there. Both projects can live in this Git repository; no Git submodule is
needed. Lake's project generator may initialize Git automatically, so create
nested project files manually when adding one here.

Keep build artifacts and temporary downloads out of Git. No API credentials
belong in this repository.
