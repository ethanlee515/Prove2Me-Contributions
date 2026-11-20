-- Prove2Me definition source: https://prove2.me/theorems/07f37f0e-ee46-4b93-b065-394eb61dcad9
import Mathlib
import Definitions.Def_CentralStrQ_Machine
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main

open CentralStrQ WordRAM

/-!
# Dynamic string data structures on the word RAM, and their query families

Boneh, Fried, Golan, Kraus, *Dynamic LZ77: No Space for Improvement*, STOC 2027 submission
(manuscript sha256 2a15e146…): footnote 1, p. 1 (PDF 3) (`Õ` in the current length); §4.1,
p. 16 (PDF 18) (edit operations and dynamic algorithms); Definition 4.7, p. 18 (PDF 20)
(LZ77-queries); Problems 2 and 3, pp. 6-7 (PDF 8-9) (LO and IPM); Lemma 7.5, p. 41 (PDF 43)
(LPF′ queries); Definition 9.1, p. 54 (PDF 56) (tree oracle).

**Formalization Note.**
* **Machine.** The published deterministic word RAM `CentralStrQ` (Hagerup's multiplication
  instruction set plus `udiv`/`umod`, unit cost, width-generic programs, `ticks` = executed
  instructions, `maxAddr` = one more than the largest address read or written during the run).
  Characters are natural numbers.
* **Compressed input.** An LZ-like parsing is given as a list of tokens: `lit c` (the
  one-character phrase `c`) or `copy len src` (a phrase of length `len ≥ 1` that copies, character
  by character, the text starting at the earlier 1-based position `src < a`, `a` the phrase's
  start; overlap allowed). `decode` rebuilds the string. Every LZ-like parsing with a chosen
  earlier occurrence for each phrase is such a token list and conversely; `z′` is the number of
  tokens. Input layout (`initLayout`): `z′`, then two words per token, `(0, c)` for `lit c` and
  `(len, src)` for `copy len src`.
* **Online protocol** (pattern of `GlobalUpdatesFO_Upper_DataStructure`, not imported). The
  initialization run starts on `loadMem (initLayout toks) rest` with an arbitrary `rest`. Each
  later operation writes its code into cells `0, …, |code|` (cell `0` = `|code|`) of the memory
  left by the previous run (`writeInput`), and the same program runs again from instruction `0`
  with fresh `ticks` and `maxAddr`. Operation codes: `[0, i, σ]` substitution, `[1, i]` deletion,
  `[2, i, σ]` insertion, `3 :: q` a query with code `q`. A query's answer is read from cells
  `0, 1, …` of the memory at the end of its run.
* **Bounds** (`ServesOnline`), per run, worst case, for every valid operation sequence:
  `Õ(f)` with current length `n` is `otilde c C n f = C·(f + 1)·(log₂(n + 2))^c`. The
  initialization run takes at most `Õ(z′)` steps and has `maxAddr ≤ Õ(z′)` (`n = |S|`); an edit
  run `S → S′` takes at most `Õ(editCost(n, z))` steps with `(n, z)` of `S`, and has
  `maxAddr ≤ Õ(max(z, z_new))` with the larger of the two lengths; a query run takes at most
  `Õ(1)` steps, has `maxAddr ≤ Õ(z)` and leaves a correct answer.
* **Word width.** Every width `w` with `2^w ≥ (N + M + 2)^c_w`, i.e. `w ≥ c_w·log₂(N + M + 2)`
  (the standard `w = Ω(log N)` of the word RAM), is allowed, `N` the largest length of the string
  over the sequence and `M` the largest word of the input layout and of all operation codes (so
  `M` bounds every character, index and `z′`). Indirect addresses are single words, so the width
  must leave room for the `Õ(z)` cells of the structure: a linear condition `2^w ≥ c_w·(N + M + 2)`
  would cap the addressable memory at `O(N)` cells, below `Õ(z)` when `z` is close to `n`.
* **Answer layouts.** LZ77-queries: `LZLength` one word; `SelectPhrase`, `ContainingPhrase` two
  words `a, b`. IPM: `0` (no occurrence) or `1, a, b, d` with `(a, b, d)` the arithmetic
  progression `{a, a + d, …, b}` of the occurrences (as positions of `S`). LO: the leftmost
  occurrence, or `0` if none. LPF′: one word. Tree oracle: the parent (`0` for the root `n + 1`),
  or the leaf bit (`1` leaf, `0` internal).
-/

/-! ## Compressed input -/

/-- A phrase of an LZ-like parsing with its source. -/
inductive Token where
  | lit (c : ℕ)
  | copy (len src : ℕ)

/-- Append `k` characters copied one at a time from position `src` on (1-based). -/
def copyChars (X : List ℕ) (src : ℕ) : ℕ → List ℕ
  | 0 => X
  | k + 1 => copyChars X src k ++ [(copyChars X src k).getD (src + k - 1) 0]

/-- Append the phrase of one token. -/
def Token.decodeStep (X : List ℕ) : Token → List ℕ
  | .lit c => X ++ [c]
  | .copy len src => copyChars X src len

/-- The string described by a token list. -/
def decode (toks : List Token) : List ℕ := toks.foldl Token.decodeStep []

/-- A token is valid as the phrase starting at position `a`: a copy has length `≥ 1` and an
earlier source position `src ∈ [1..a − 1]`. -/
def Token.Valid (a : ℕ) : Token → Prop
  | .lit _ => True
  | .copy len src => 1 ≤ len ∧ 1 ≤ src ∧ src < a

/-- Every token is valid at its starting position. -/
def TokensValid (toks : List Token) : Prop :=
  ∀ (t : ℕ) (ht : t < toks.length), toks[t].Valid ((decode (toks.take t)).length + 1)

/-- The two input words of a token. -/
def Token.words : Token → List ℕ
  | .lit c => [0, c]
  | .copy len src => [len, src]

/-- The input layout of the initialization run: `z′`, then the words of each token. -/
def initLayout (toks : List Token) : List ℕ := toks.length :: (toks.map Token.words).flatten

/-! ## Operations and query families -/

/-- A query family: queries, their validity on the current string, their codes, and the
correct-answer relation (`Correct S q out`: the output cells `out 0, out 1, …` hold a correct
answer to `q` on `S`). -/
structure QueryFamily where
  Q : Type
  Valid : List ℕ → Q → Prop
  code : Q → List ℕ
  Correct : List ℕ → Q → (ℕ → ℕ) → Prop

/-- An operation: an edit or a query. -/
inductive Op (Q : Type) where
  | edit (e : Edit ℕ)
  | query (q : Q)

/-- The code of an edit. -/
def Edit.code : Edit ℕ → List ℕ
  | .subst i c => [0, i, c]
  | .del i => [1, i]
  | .ins i c => [2, i, c]

/-- The code of an operation. -/
def Op.code (F : QueryFamily) : Op F.Q → List ℕ
  | .edit e => e.code
  | .query q => 3 :: F.code q

/-- Validity of an operation on the current string. -/
def Op.Valid (F : QueryFamily) (S : List ℕ) : Op F.Q → Prop
  | .edit e => e.Valid S.length
  | .query q => F.Valid S q

/-- The string after an operation (queries leave it unchanged). -/
def Op.apply {Q : Type} (S : List ℕ) : Op Q → List ℕ
  | .edit e => e.apply S
  | .query _ => S

/-- The strings `S_0, S_1, …, S_T`: `S_t` is the string before operation `t`. -/
def strSeq {Q : Type} (S0 : List ℕ) (ops : List (Op Q)) : List (List ℕ) :=
  ops.scanl (fun S o => Op.apply S o) S0

/-- Every operation is valid on the string it is applied to. -/
def OpsValid (F : QueryFamily) (S0 : List ℕ) (ops : List (Op F.Q)) : Prop :=
  ∀ (t : ℕ) (ht : t < ops.length), Op.Valid F ((strSeq S0 ops).getD t []) ops[t]

/-- `N`: the largest length of the string over the sequence. -/
def maxLen {Q : Type} (S0 : List ℕ) (ops : List (Op Q)) : ℕ :=
  ((strSeq S0 ops).map List.length).foldr max 0

/-- `M`: the largest word of the input layout and of all operation codes. -/
def maxWord (F : QueryFamily) (toks : List Token) (ops : List (Op F.Q)) : ℕ :=
  (initLayout toks ++ (ops.map (Op.code F)).flatten).foldr max 0

/-! ## The online run -/

/-- The memory an operation run starts on: `mem` with the code `c` written into cells
`0, 1, …, |c|` (cell `0` holds `|c|`, cell `1 + i` holds `c[i]`); every other cell is kept. -/
def writeInput {w : Width} (mem : Memory w) (c : List ℕ) : Memory w := fun a =>
  if a = 0 then BitVec.ofNat w.bits c.length
  else if a ≤ c.length then BitVec.ofNat w.bits (c.getD (a - 1) 0) else mem a

open Classical in
/-- The final state of the run of `P` from `mem` (the state at the first halting step; the
initial state if the run never halts). -/
noncomputable def finalState (P : Program) {w : Width} (mem : Memory w) : CentralStrQ.State w :=
  if h : ∃ k, (runN P k (State.init mem)).halted = true then
    runN P (Nat.find h) (State.init mem)
  else State.init mem

/-- The memory after the initialization run on `mem0` and then one run per code in `codes`. -/
noncomputable def memAfter (P : Program) {w : Width} (mem0 : Memory w) (codes : List (List ℕ)) :
    Memory w :=
  codes.foldl (fun m c => (finalState P (writeInput m c)).mem) (finalState P mem0).mem

/-- `Õ(f)` in the current length `n`: `C·(f + 1)·(log₂(n + 2))^c`. -/
noncomputable def otilde (c : ℕ) (C : ℝ) (n : ℕ) (f : ℝ) : ℝ :=
  C * (f + 1) * Real.logb 2 ((n : ℝ) + 2) ^ c

/-- The requirement on the run of one operation `o` on the current string `S`, started on
memory `mem`: an edit halts within `Õ(editCost(|S|, z(S)))` steps and touches addresses below
`Õ(max(z(S), z(S′)))` (length `max(|S|, |S′|)`); a query halts within `Õ(1)` steps, touches
addresses below `Õ(z(S))` and leaves a correct answer in cells `0, 1, …`. -/
def OpRunOK (F : QueryFamily) (editCost : ℕ → ℕ → ℝ) (P : Program) (c : ℕ) (C : ℝ)
    (S : List ℕ) {w : Width} (mem : Memory w) : Op F.Q → Prop
  | .edit e =>
      RunsWithin P mem (otilde c C S.length (editCost S.length (z S)))
        (fun _ reach => (reach : ℝ) ≤
          otilde c C (max S.length (e.apply S).length) ((max (z S) (z (e.apply S)) : ℕ) : ℝ))
  | .query q =>
      RunsWithin P mem (otilde c C S.length 1)
        (fun out reach => (reach : ℝ) ≤ otilde c C S.length (z S) ∧
          F.Correct S q (fun a => (out a).toNat))

/-- **`P` is a dynamic data structure for the query family `F`** with edit cost `editCost`,
constants `c, C` and width constant `cw`: for every valid token list (an LZ-like parsing of
`S_0` with `z′` phrases), every finite sequence of valid operations, every word width `w` with
`(N + M + 2)^cw ≤ 2^w` (that is, `w ≥ cw·log₂(N + M + 2)`) and every content `rest` of the
uninitialized memory,
* the initialization run halts within `Õ(z′)` steps and touches addresses below `Õ(z′)`;
* the run of each operation `t` (on the memory left by the previous run, with the operation's
  code written in) satisfies `OpRunOK` for the current string `S_t`. -/
def ServesOnline (F : QueryFamily) (editCost : ℕ → ℕ → ℝ) (P : Program) (c : ℕ) (C : ℝ)
    (cw : ℕ) : Prop :=
  ∀ (toks : List Token) (ops : List (Op F.Q)) (w : Width) (rest : Memory w),
    TokensValid toks →
    OpsValid F (decode toks) ops →
    (maxLen (decode toks) ops + maxWord F toks ops + 2) ^ cw ≤ 2 ^ w.bits →
    RunsWithin P (loadMem (initLayout toks) rest)
        (otilde c C (decode toks).length (toks.length : ℝ))
        (fun _ reach => (reach : ℝ) ≤ otilde c C (decode toks).length (toks.length : ℝ)) ∧
    ∀ (t : ℕ) (ht : t < ops.length),
      OpRunOK F editCost P c C ((strSeq (decode toks) ops).getD t [])
        (writeInput (memAfter P (loadMem (initLayout toks) rest)
          ((ops.take t).map (Op.code F))) (Op.code F ops[t])) ops[t]

/-! ## The query families -/

/-- LZ77-queries (Definition 4.7). -/
inductive LZQuery where
  | lzLength (i : ℕ)
  | selectPhrase (i : ℕ)
  | containingPhrase (i : ℕ)

/-- The LZ77-query family: `LZLength_S(i)` (`i ∈ [1..n]`) is the number of phrases of
`LZ77(S[1..i])`; `SelectPhrase_S(i)` (`i ∈ [1..z]`) is the `i`-th phrase `(a, b)` of `LZ77(S)`;
`ContainingPhrase_S(i)` (`i ∈ [1..n]`) is the phrase `(a, b) ∈ LZ77(S)` with `i ∈ [a..b]`. -/
def lzQueries : QueryFamily where
  Q := LZQuery
  Valid S
    | .lzLength i => 1 ≤ i ∧ i ≤ S.length
    | .selectPhrase i => 1 ≤ i ∧ i ≤ z S
    | .containingPhrase i => 1 ≤ i ∧ i ≤ S.length
  code
    | .lzLength i => [0, i]
    | .selectPhrase i => [1, i]
    | .containingPhrase i => [2, i]
  Correct S
    | .lzLength i, out => out 0 = z (S.take i)
    | .selectPhrase i, out => (LZ77 S)[i - 1]? = some (out 0, out 1)
    | .containingPhrase i, out => (out 0, out 1) ∈ LZ77 S ∧ out 0 ≤ i ∧ i ≤ out 1

/-- `k` is an occurrence of `P` in `X`: `X[k..k + |P| − 1] = P` (1-based). -/
def IsOcc (X P : List ℕ) (k : ℕ) : Prop :=
  1 ≤ k ∧ k + P.length ≤ X.length + 1 ∧ (X.drop (k - 1)).take P.length = P

/-- The arithmetic progression `(a, b, d) = {a, a + d, …, b}`: a valid triple has
`b = a + t·d` for some `t`, and its set is `{a + s·d | s ∈ [0..t]}`. -/
def IsAP (a b d : ℕ) : Prop := ∃ t : ℕ, b = a + t * d

/-- The set of the progression `(a, b, d)`. -/
def apSet (a b d : ℕ) : Set ℕ := {x | a ≤ x ∧ x ≤ b ∧ ∃ s : ℕ, x = a + s * d}

/-- An IPM query: `P = S[ip..jp]`, `T = S[it..jt]`. -/
structure IPMQuery where
  ip : ℕ
  jp : ℕ
  it : ℕ
  jt : ℕ

/-- The IPM query family (Problem 3): valid when `P = S[ip..jp]` is a substring, `T = S[it..jt]`
is a (possibly empty) substring and `|T| < 2|P|`; the answer is `0` when `P` does not occur in
`T`, otherwise `1, a, b, d` with `{a, a + d, …, b}` exactly the starting positions in `S` of the
occurrences of `P` inside `T`. -/
def ipmQueries : QueryFamily where
  Q := IPMQuery
  Valid S q := 1 ≤ q.ip ∧ q.ip ≤ q.jp ∧ q.jp ≤ S.length ∧ 1 ≤ q.it ∧ q.it ≤ q.jt + 1 ∧
    q.jt ≤ S.length ∧ q.jt + 1 - q.it < 2 * (q.jp + 1 - q.ip)
  code q := [q.ip, q.jp, q.it, q.jt]
  Correct S q out :=
    let occ : Set ℕ := {k | q.it ≤ k ∧ k + (q.jp - q.ip) ≤ q.jt ∧ IsOcc S (sub S q.ip q.jp) k}
    (out 0 = 0 ∧ occ = ∅) ∨
      (out 0 = 1 ∧ IsAP (out 1) (out 2) (out 3) ∧ apSet (out 1) (out 2) (out 3) = occ)

/-- An LO query: `P = S[i..j]` and an optional hypothetical edit. -/
structure LOQuery where
  i : ℕ
  j : ℕ
  edit : Option (Edit ℕ)

/-- The LO query family (Problem 2): valid when `S[i..j]` is a (possibly empty) substring and the
optional edit is valid on `S`; the answer is the leftmost occurrence of `P = S[i..j]` in `S`
(no edit) or in `S′` = the edited string (edit given), or `0` if there is none. The edit is
hypothetical: queries never change the maintained string (`Op.apply`). -/
def loQueries : QueryFamily where
  Q := LOQuery
  Valid S q := 1 ≤ q.i ∧ q.i ≤ q.j + 1 ∧ q.j ≤ S.length ∧
    ∀ e, q.edit = some e → e.Valid S.length
  code q := match q.edit with
    | none => [q.i, q.j, 0]
    | some e => q.i :: q.j :: 1 :: e.code
  Correct S q out :=
    let X := match q.edit with
      | none => S
      | some e => e.apply S
    let P := sub S q.i q.j
    (out 0 = 0 ∧ ∀ k, ¬ IsOcc X P k) ∨ (IsOcc X P (out 0) ∧ ∀ k < out 0, ¬ IsOcc X P k)

/-- The LPF′ query family (Lemma 7.5): given `i ∈ [1..n]`, report `LPF′_S(i)`. -/
def lpfQueries : QueryFamily where
  Q := ℕ
  Valid S i := 1 ≤ i ∧ i ≤ S.length
  code i := [i]
  Correct S i out := out 0 = lpf' S i

/-- A tree-oracle query (Definition 9.1). -/
inductive TreeQuery where
  | parent (i : ℕ)
  | isLeaf (i : ℕ)

/-- The tree-oracle family for the LPF′-tree (nodes `[1..n+1]`, Definition 9.1, Lemma 9.6): the
parent of `i` (`i + LPF′_S(i)` for `i ∈ [1..n]`, and `0` for the root `n + 1`), and whether `i`
is a leaf (`1`) or not (`0`). -/
def treeQueries : QueryFamily where
  Q := TreeQuery
  Valid S
    | .parent i => 1 ≤ i ∧ i ≤ S.length + 1
    | .isLeaf i => 1 ≤ i ∧ i ≤ S.length + 1
  code
    | .parent i => [0, i]
    | .isLeaf i => [1, i]
  Correct S
    | .parent i, out => out 0 = if i ≤ S.length then treeParent S i else 0
    | .isLeaf i, out => (out 0 = 1 ∧ IsLeaf S i) ∨ (out 0 = 0 ∧ ¬ IsLeaf S i)

end DynLZ77.Main
