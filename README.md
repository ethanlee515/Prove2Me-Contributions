# STOC formalization issues

This repository collects Lean-checked findings about STOC 2027 submissions and
their Prove2Me formalizations. For submission 173, we disproved the published
Lean lemma. For the other four submissions, we proved specific shortcuts in
the formal models. Those witnesses do not prove the headline theorems or show
that the papers' claims are false.

The four shortcut ideas fit in one sentence each. Their Lean files are
120–306 lines, including the machine checks needed to make the ideas precise.
They establish their points through the formal models without reproducing the
papers' main arguments. Whether any shortcut yields an accepted proof of a
headline theorem remains open.

## Findings at a glance

| Submission | Statement | Finding | Evidence |
| --- | --- | --- | --- |
| 167 | [Theorem 1.1](https://prove2.me/theorems/a3e55186-d849-4195-941b-7db80ced1cd1) | The random-tape length can tell a fixed program a fact about the input size that it cannot compute. | [Lean witness](Audit/TapeAdvice167.lean) |
| 173 | Lemma D.17 | With no students, all student checks pass vacuously even when the public tape has an unused bit. Prove2Me accepted the disproof. | [Proof](DisproofD17.lean) · [verification](VERIFICATION.md) |
| 1131 | [Theorem 1.1](https://prove2.me/theorems/29c7bfe7-4943-4dcd-923b-b8eb97b03679) | Data left in memory after a string shrinks can still affect a later answer without being charged as current storage. | [Lean witness](Audit/DynamicSpace1131.lean) |
| 1352 | [Theorem 1](https://prove2.me/theorems/5d3c84ce-e1a1-4d28-86b9-f6e2bb45ac50) | The cost counter charges a list lookup as though it were a constant-time array lookup. | [Lean witness](Audit/ListLookup1352.lean) |
| 1508 | [Theorem 5.1](https://prove2.me/theorems/753e9c1f-34f7-4686-95dd-9ea08a19e66b) | Memory addresses can carry information, but their bits are omitted from the working-space count. | [Lean witness](Audit/SparseAddresses1508.lean) |

## Reproduce the checks

Run `lake build Audit` and `lake env leanchecker Audit` for the four model
witnesses. Run `lake build StatementMatch` for the D.17 disproof and its match
to the published Lean statement. See the [technical witness notes](AUDIT_NOTES.md)
and [local development guide](DEVELOPMENT.md) for details.

## Contributors

Project contributors, listed alphabetically by family name:

- Yu-Fang Chen (Academia Sinica)
- Kai-Min Chung (Academia Sinica)
- Shih-Han Hung (National Taiwan University)
- Yi Lee (University of Maryland)
