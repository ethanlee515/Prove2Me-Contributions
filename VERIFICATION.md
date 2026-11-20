# Submission 173, Lemma D.17: local Lean verification

**Result: the negation of the published Lean statement compiles in the pinned
environment. No proof was submitted or published.**

## Sources and environment

The published declaration and its two definition modules were fetched from
`prove2me/formalpedia` at commit
`d2016173f14e0d37b2023e4d58083d99017855eb`. The current default-branch
versions of these three files matched that snapshot when checked on 2026-11-19.
The local files are:

- `Theorems/Thm_MatchIndiff_PublicSM_lemma_D_17.lean`
- `Definitions/Def_MatchIndiff_PublicSM_Model.lean`
- `Definitions/Def_MatchIndiff_PublicSM_Tape.lean`

`lean-toolchain` pins Lean 4.33.1. `lakefile.toml` pins mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. `lake-manifest.json` records
the resolved dependencies. The downloaded packages and compiled cache live in
the ignored `.lake` directory.

The audit PDF's embedded `173_candidate.lean` was extracted byte for byte as
`SourceCandidate173.lean` (SHA-256:
`69880FA693960828B8A787EE2D310908C67E89459A041DDDA90D73BE5AE2452A`).
It compiles in the pinned environment with two unused-binder warnings.

## Machine-checked result

`DisproofD17.lean` defines `D17Statement` and proves `not_D17Statement :
¬ D17Statement`. The proof uses `n = m = 0`, empty profiles, a procedure that
stops immediately, and the board `[true]`. All student checks hold because
there are no students. The public pair list is empty, so replay sees the one
unused bit and returns `none`, contradicting the existential replay conclusion.

The file imports only mathlib and the published Model and Tape definitions. It
does **not** import the published theorem's `by sorry` placeholder. Its
`#print axioms` result is:

```text
'MatchIndiff.PublicSM.not_D17Statement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` dependency. `StatementMatch.lean` separately imports the
published declaration and checks that it inhabits `D17Statement`; this checks
the exact target type. That file uses the published open theorem only for the
type check and is not imported by the disproof.

## Reproduce

```powershell
lake update
lake build StatementMatch
lake env lean SourceCandidate173.lean
```

The final `lake build StatementMatch` run completed successfully with 8712 jobs.
The only `sorry` warning came from the published Open theorem source. No local
commit, push, submission, or other external write was made.

## Prepared submission

`Solutions/Sol_MatchIndiff_PublicSM_lemma_D_17.lean` adapts the same proof to
Prove2Me's required top-level `theorem solution : ¬ (∀ ..., ...)` form. It
compiles locally with `autoImplicit false`. `StatementMatch.lean` also checks
that `solution` has the negation of the exact published theorem type. The
`#print axioms solution` output is `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx`. The
prepared public explanation, including joint-discovery credit, is in
`submission_explanation.md`; `SUBMISSION_DRAFT.md` lists the exact API fields.
No API key has been used and nothing has been submitted.
