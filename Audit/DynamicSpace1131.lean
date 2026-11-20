import Definitions.Def_DynLZ77_Main_DataStructure

/-! # Paper 1131, Theorem 1.1

On a single valid history a RAM program meets the published initialization,
edit, and LZ77-query bounds. A word written at initialization survives deletion
of the entire string. Truncating memory to the empty string's space allowance
changes the answer to a valid query after reinsertion.
-/

namespace Audit.DynamicSpace1131

open WordRAM CentralStrQ DynLZ77.Main

def width : Width := ⟨4, by decide⟩

/-- Initialization writes one to cell 7. Edits leave it alone. The LZLength
query copies it to the answer cell. Word 1 distinguishes the three cases on
this history. -/
def program : CentralStrQ.Program :=
  [.branch .eq (.memory (.direct 1)) (.immediate 0) 3,
   .branch .eq (.memory (.direct 1)) (.immediate 3) 5,
   .halt,
   .copy (.direct 7) (.immediate 1),
   .halt,
   .copy (.direct 0) (.memory (.direct 7)),
   .halt]

def tokens : List Token := [.lit 1]

def history : List (Op lzQueries.Q) :=
  [.edit (.del 1), .edit (.ins 1 1), .query (.lzLength 1)]

private abbrev initial (rest : Memory width) :=
  loadMem (initLayout tokens) rest

/-- Persistent memory after initialization and the first `n` operations. -/
noncomputable def after (rest : Memory width) (n : ℕ) : Memory width :=
  memAfter program (initial rest) ((history.take n).map (Op.code lzQueries))

private theorem final_at (mem : Memory width) (k : ℕ)
    (hk : (runN program k (.init mem)).halted = true)
    (hmin : ∀ j < k, (runN program j (.init mem)).halted ≠ true) :
    finalState program mem = runN program k (.init mem) := by
  classical
  rw [finalState, dif_pos ⟨k, hk⟩, (Nat.find_eq_iff _).mpr ⟨hk, hmin⟩]

private theorem init_final (rest : Memory width) :
    finalState program (initial rest) = runN program 3 (.init (initial rest)) := by
  apply final_at _ _ rfl
  intro j hj
  interval_cases j <;> exact Bool.noConfusion

private theorem delete_final (mem : Memory width) :
    finalState program (writeInput mem [1, 1]) = runN program 3 (.init (writeInput mem [1, 1])) := by
  apply final_at _ _ rfl
  intro j hj
  interval_cases j <;> exact Bool.noConfusion

private theorem insert_final (mem : Memory width) :
    finalState program (writeInput mem [2, 1, 1]) =
      runN program 3 (.init (writeInput mem [2, 1, 1])) := by
  apply final_at _ _ rfl
  intro j hj
  interval_cases j <;> exact Bool.noConfusion

private theorem query_final (mem : Memory width) :
    finalState program (writeInput mem [3, 0, 1]) =
      runN program 4 (.init (writeInput mem [3, 0, 1])) := by
  apply final_at _ _ rfl
  intro j hj
  interval_cases j <;> exact Bool.noConfusion

private theorem stored_after_delete (rest : Memory width) : after rest 1 7 = 1 := by
  change ((finalState program (writeInput (finalState program (initial rest)).mem [1, 1])).mem 7) = 1
  rw [delete_final, init_final]
  rfl

private theorem stored_after_insert (rest : Memory width) : after rest 2 7 = 1 := by
  change (finalState program (writeInput (after rest 1) [2, 1, 1])).mem 7 = 1
  rw [insert_final]
  exact stored_after_delete rest

private theorem z_one : z ([1] : List ℕ) = 1 := by decide +kernel
private theorem z_empty : z ([] : List ℕ) = 0 := by decide +kernel

private noncomputable abbrev editCost (n zz : ℕ) := min ((n : ℝ) ^ ((2 : ℝ) / 3)) (zz : ℝ)

/-- The concrete token input, edits, and query satisfy the premises and
per-run obligations of `ServesOnline` at this history, with c = 0, C = 4,
and word-width constant 1. Initial unused memory is arbitrary. -/
theorem history_meets_bounds (rest : Memory width) :
    TokensValid tokens ∧ OpsValid lzQueries (decode tokens) history ∧
    (maxLen (decode tokens) history + maxWord lzQueries tokens history + 2) ^ 1 ≤ 2 ^ width.bits ∧
    RunsWithin program (initial rest)
      (otilde 0 4 (decode tokens).length tokens.length)
      (fun _ reach => (reach : ℝ) ≤ otilde 0 4 (decode tokens).length tokens.length) ∧
    ∀ (t : ℕ) (ht : t < history.length),
      OpRunOK lzQueries editCost program 0 4 ((strSeq (decode tokens) history).getD t [])
        (writeInput (after rest t) (Op.code lzQueries history[t])) history[t] := by
  refine ⟨?_, ?_, by decide, ?_, ?_⟩
  · intro t ht
    change t < 1 at ht
    interval_cases t
    trivial
  · intro t ht
    change t < 3 at ht
    interval_cases t <;> exact ⟨by decide, by decide⟩
  · refine ⟨3, rfl, ?_, ?_⟩
    change ((3 : ℕ) : ℝ) ≤ otilde 0 4 1 ((1 : ℕ) : ℝ)
    norm_num [otilde]
    change ((8 : ℕ) : ℝ) ≤ otilde 0 4 1 ((1 : ℕ) : ℝ)
    norm_num [otilde]
  · intro t ht
    change t < 3 at ht
    interval_cases t
    · refine ⟨3, rfl, ?_, ?_⟩
      change ((3 : ℕ) : ℝ) ≤ otilde 0 4 1 (editCost 1 (z [1]))
      norm_num [otilde, editCost, z_one]
      change ((2 : ℕ) : ℝ) ≤ otilde 0 4 1 ((max (z [1]) (z ([] : List ℕ)) : ℕ) : ℝ)
      norm_num [otilde, z_one, z_empty]
    · refine ⟨3, rfl, ?_, ?_⟩
      change ((3 : ℕ) : ℝ) ≤ otilde 0 4 0 (editCost 0 (z ([] : List ℕ)))
      norm_num [otilde, editCost, z_empty, Real.zero_rpow]
      change ((2 : ℕ) : ℝ) ≤ otilde 0 4 1 ((max (z ([] : List ℕ)) (z [1]) : ℕ) : ℝ)
      norm_num [otilde, z_one, z_empty]
    · refine ⟨4, rfl, ?_, ?_, ?_⟩
      change ((4 : ℕ) : ℝ) ≤ otilde 0 4 1 1
      norm_num [otilde]
      change ((8 : ℕ) : ℝ) ≤ otilde 0 4 1 (z [1])
      norm_num [otilde, z_one]
      change ((after rest 2 7).toNat) = z ([1] : List ℕ)
      rw [stored_after_insert, z_one]
      rfl

/-- Replay insertion and the query from the memory supplied at the empty string. -/
noncomputable def replayAnswer (mem : Memory width) : ℕ :=
  let grown := (finalState program (writeInput mem [2, 1, 1])).mem
  ((finalState program (writeInput grown [3, 0, 1])).mem 0).toNat

/-- At the empty string the cap is four words and cell 7 still holds one.
Keeping addresses below four makes the same subsequent query return zero. -/
theorem truncation_changes_answer (rest : Memory width) :
    (strSeq (decode tokens) history).getD 1 [] = [] ∧
    otilde 0 4 0 (z ([] : List ℕ)) = 4 ∧
    after rest 1 7 = 1 ∧
    replayAnswer (after rest 1) = 1 ∧
    replayAnswer (fun a => if a < 4 then after rest 1 a else 0) = 0 := by
  refine ⟨rfl, by norm_num [otilde, z_empty], stored_after_delete rest, ?_, ?_⟩
  · dsimp only [replayAnswer]
    rw [query_final, insert_final]
    change (after rest 1 7).toNat = 1
    rw [stored_after_delete]
    rfl
  · dsimp only [replayAnswer]
    rw [query_final, insert_final]
    rfl

#print axioms history_meets_bounds
#print axioms truncation_changes_answer

end Audit.DynamicSpace1131
