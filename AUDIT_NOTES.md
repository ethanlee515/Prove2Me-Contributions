# Technical notes on the four model witnesses

The files in `Audit/` prove the specific claims below against the pinned Lean
definitions. They do not prove the corresponding headline theorems, and they
are not disproofs of the source papers. Each module prints the axioms used by
its witness; the results use only `propext`, `Classical.choice`, and `Quot.sound`.

## Submission 167: random-tape length as advice

[TapeAdvice167.lean](Audit/TapeAdvice167.lean) chooses the tape length to be one
if the input size belongs to a set `H`, and zero otherwise. For every possible
draw, the same finite initializer skips the four encoded parameters and
outputs the next marker. Its step bound is the total number of parameter
digits plus five, and its stack bound is the encoded parameter length plus
three. Taking `H` to be the halting problem gives a provably uncomputable tape
length even for `n ≥ 2`, `r = k = 2`, and `m = 8`.

The headline theorem also requires updates, subtraction, and successful
hypergraph recovery for every valid stream. This witness establishes the
nonuniform advice channel in its model, not those further obligations.

## Submission 1131: persistent memory after shrinkage

[DynamicSpace1131.lean](Audit/DynamicSpace1131.lean) gives a program that writes
cell 7 during initialization. After deletion leaves the empty string, the
current space allowance is four words, but the cell survives. The LZ-length
query after reinsertion returns one; clearing addresses four and above at the
empty string makes that same query return zero. The proof checks the bounds
for this history with arbitrary initial unused memory.

The headline theorem quantifies over all valid operation histories. This
witness establishes the storage-model discrepancy for one concrete history.

## Submission 1352: uncharged list traversal

[ListLookup1352.lean](Audit/ListLookup1352.lean) analyzes the published
`relabel` loop. Reading entry `i` from the head of a list visits exactly
`i + 1` cells, while the formal interpreter charges one tick per iteration.
For a list of length `s`, the traversals visit `s*(s+1)/2` cells but the
interpreter charges `s` ticks. The counted lookup returns the same value as
`List.getD`, and the interpreter returns the same labels.

The headline theorem also needs the norm approximation and expected cost of
the entire `pqNorm` program. This witness isolates the preprocessing cost.

## Submission 1508: information in memory addresses

[SparseAddresses1508.lean](Audit/SparseAddresses1508.lean) stores one at each
address encoding a pair `(i, block i)` for `k` blocks of `k` bits each. The
resulting memories are pairwise distinct. Each occupied cell contributes
three bits for the rational value one. For each `k`, one program realizes all
`2^(k*k)` memories on selected coin tapes. Each of those runs has peak
`BitRAM.workingBits ≤ 5*k+5`, including the address register. The program
scans `2^(2*k)` candidate addresses, so this witness does not establish the
headline time bound.

The headline theorem also requires constructors and samplers for approximate
Nash equilibria in both RAM models, with separate time and output guarantees.

## Sources

The definition files carry their public Prove2Me URLs in their headers. The
source for these cases is the pinned [Formalpedia snapshot](https://github.com/prove2me/formalpedia/tree/d2016173f14e0d37b2023e4d58083d99017855eb/envs/0df444a/Definitions),
supplemented by the published definition pages for the dynamic-string RAM and
its imports.
