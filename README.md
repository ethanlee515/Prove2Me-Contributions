# STOC formalization issues

This repository records reproducible investigations of statements in STOC
formalizations. A claim of disproof is recorded as verified here only after
its negation compiles against the exact published statement and pinned
dependencies. A formal counterexample and a claim about the corresponding
paper are separate conclusions.

## Contributors

Project contributors, listed alphabetically by family name:

- Yu-Fang Chen (Academia Sinica)
- Kai-Min Chung (Academia Sinica)
- Shih-Han Hung (National Taiwan University)
- Yi Lee (University of Maryland)

## Case index

| Submission | Statement | Finding | Evidence |
| --- | --- | --- | --- |
| 167 | [Theorem 1.1](https://prove2.me/theorems/a3e55186-d849-4195-941b-7db80ced1cd1) | A fixed initializer reads an arbitrary advice bit from the length of a one-symbol coin tape. | [TapeAdvice167.lean](Audit/TapeAdvice167.lean) |
| 173 | Lemma D.17 | The published Lean statement is false for `n = m = 0`; the disproof was accepted by Prove2Me. | [Verification](VERIFICATION.md), [proof](DisproofD17.lean), [type check](StatementMatch.lean), [submission record](SUBMISSION_DRAFT.md) |
| 1131 | [Theorem 1.1](https://prove2.me/theorems/29c7bfe7-4943-4dcd-923b-b8eb97b03679) | An LZ77 query reads a cell retained across deletion and reinsertion while each run meets its address bound. | [DynamicSpace1131.lean](Audit/DynamicSpace1131.lean) |
| 1352 | [Theorem 1](https://prove2.me/theorems/5d3c84ce-e1a1-4d28-86b9-f6e2bb45ac50) | Relabelling charges exactly `s` ticks for a pass whose indexed list reads visit `s*(s+1)/2` cells. | [ListLookup1352.lean](Audit/ListLookup1352.lean) |
| 1508 | [Theorem 5.1](https://prove2.me/theorems/753e9c1f-34f7-4686-95dd-9ea08a19e66b) | The sparse memory addresses distinguish `2^(k*k)` states with the same charge of `3*k` bits. | [SparseAddresses1508.lean](Audit/SparseAddresses1508.lean) |

## Checking the four shortcut witnesses

Run `lake build Audit` at the repository root with the pinned Lean 4.33.1 and
mathlib `0df444a` environment. Each module prints the axioms of its witness.
The witnesses use only `propext`, `Classical.choice`, and `Quot.sound`.
Run `lake env leanchecker Audit` to replay the four compiled modules.

- **167.** Choose the tape length to be one if the input size belongs to a set
  `H`, and zero otherwise. For every possible draw, the same finite machine
  skips the four encoded parameters and outputs the next marker. Its step
  bound is the total number of parameter digits plus five. Its stack bound is
  the encoded parameter length plus three. Instantiating `H` with the halting
  problem gives a provably uncomputable tape length even for `n ≥ 2`,
  `r = k = 2`, and `m = 8`. The headline also requires updates,
  subtraction, and successful hypergraph recovery for every valid stream.
- **1131.** The program writes cell 7 during initialization. After deletion
  leaves the empty string, the current space allowance is four words. The
  cell survives, and the LZ length query after reinsertion returns the correct
  answer of one. Clearing addresses four and above at the empty string makes
  the same query return zero. The proof checks the bounds for this history
  with arbitrary initial unused memory. The headline quantifies over all
  valid operation histories.
- **1352.** The published `relabel` loop reads entry `i` from the head of its
  list. The counted lookup returns the same value as `List.getD` and visits
  exactly `i+1` cells for an in-range index. The formal interpreter returns
  the same labels and charges one tick per iteration. The headline also needs
  the norm approximation and expected cost of the entire `pqNorm` program.
- **1508.** Store one at each address encoding a pair `(i, block i)` for `k`
  blocks of `k` bits each. The resulting memories are pairwise distinct.
  Each occupied cell contributes three bits for the rational value one.
  For each `k`, one program realizes all `2^(k*k)` memories on selected coin
  tapes. Each of those runs has peak `BitRAM.workingBits ≤ 5*k+5`, including
  the address register. The program scans `2^(2*k)` candidate addresses.
  The headline also requires constructors and samplers for approximate Nash
  equilibria in both RAM models, with separate time and output guarantees.

The definitions carry their public Prove2Me URLs in their file headers.
The source for these cases is the pinned Formalpedia export, supplemented
by the published definition pages for the dynamic-string RAM and its imports.
[Formalpedia snapshot](https://github.com/prove2me/formalpedia/tree/d2016173f14e0d37b2023e4d58083d99017855eb/envs/0df444a/Definitions).

## Lean layout

The repository currently has one Lake project at its root. Its
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin the environment
for the indexed cases. Run `lake build StatementMatch` from this directory to
check the local disproof and its match to the published declaration.

Cases that use the same Lean and mathlib versions can be added as separate
modules in this project. If another case needs a different toolchain or
dependency revision, put its own Lake project in a subdirectory and run Lake
there. Both projects can live in this Git repository; no Git submodule is
needed. Lake's project generator may initialize Git automatically, so create
nested project files manually when adding one here.

Keep build artifacts and temporary downloads out of Git. No API credentials
belong in this repository.
