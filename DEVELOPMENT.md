# Local verification and repository layout

The repository has one Lake project at its root. `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json` pin Lean 4.33.1 and mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` for the indexed cases.

Run these commands from the repository root:

```powershell
lake build Audit
lake env leanchecker Audit
lake build StatementMatch
```

The first two commands compile and replay the four shortcut witnesses. The
last checks the D.17 disproof and its type match to the published Lean
declaration. [VERIFICATION.md](VERIFICATION.md) records that case in detail.

Cases using the same Lean and mathlib versions can be separate modules in
this project. If a new case needs a different toolchain or dependency
revision, place a separate Lake project in a subdirectory and run Lake there.
Both projects can live in one Git repository; no Git submodule is needed.
Lake's project generator may initialize Git automatically, so create nested
project files manually when adding one here.

Keep build artifacts and temporary downloads out of Git. Do not put API
credentials in this repository.
