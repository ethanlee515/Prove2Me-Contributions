import Definitions.Def_PQNormIPM1352_Main_Algorithm1

/-! # Paper 1352, Theorem 1

The published `preprocess` calls `relabel` on sorted row and column keys.
Each pass reads `sorted.getD t (0, 0)` for `t = 0, …, s - 1`. Compare the
interpreter's charge for the pass with the number of list cells visited when
performing just those reads from the head of the linked list.
-/

namespace Audit.ListLookup1352

open PQNormIPM1352.Main

/-- A literal list lookup, paired with the number of cons cells inspected. -/
def countedGetD {α : Type} (fallback : α) : List α → ℕ → α × ℕ
  | [], _ => (fallback, 0)
  | x :: _, 0 => (x, 1)
  | _ :: xs, i + 1 =>
    let (value, visits) := countedGetD fallback xs i
    (value, visits + 1)

theorem countedGetD_value {α : Type} (fallback : α) (xs : List α) (i : ℕ) :
    (countedGetD fallback xs i).1 = xs.getD i fallback := by
  induction xs generalizing i with
  | nil => simp [countedGetD]
  | cons x xs ih => cases i <;> simp [countedGetD, ih]

private theorem visits_at_index {α : Type} (fallback : α) (xs : List α) (i : ℕ)
    (hi : i < xs.length) : (countedGetD fallback xs i).2 = i + 1 := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp [countedGetD, ih i (by simpa using hi)]

private theorem sum_visits (s : ℕ) :
    2 * (∑ i ∈ Finset.range s, (i + 1)) = s * (s + 1) := by
  induction s with
  | zero => simp
  | succ s ih => rw [Finset.sum_range_succ, Nat.mul_add, ih]; ring

private abbrev Labels := Option ℕ × ℕ × (ℕ → ℕ)

/-- Thread the previous key, number of distinct keys, and label array through
one iteration of the published scan. -/
private def assign (st : Labels) (entry : ℕ × ℕ) : Labels :=
  match st.1 with
  | none => (some entry.1, 1, Function.update st.2.2 entry.2 0)
  | some prev =>
    if entry.1 = prev then (some prev, st.2.1, Function.update st.2.2 entry.2 (st.2.1 - 1))
    else (some entry.1, st.2.1 + 1, Function.update st.2.2 entry.2 st.2.1)

/-- The labels computed from the values returned by the counted list reads. -/
def literalRelabel (sorted : List (ℕ × ℕ)) : ℕ × (ℕ → ℕ) :=
  let final := (List.range sorted.length).foldl
    (fun st t => assign st (countedGetD (0, 0) sorted t).1) (none, 0, fun _ => 0)
  final.2

private theorem fold_ticks {σ α : Type} (indices : List ℕ) (s : σ) (next : σ → ℕ → σ)
    (body : ℕ → σ → Prog ℝ σ) (finish : σ → α)
    (hbody : ∀ i st, body i st = .ret (next st i)) :
    Prog.bind (indices.foldlM
        (fun st i => Prog.bind Prog.step fun _ => body i st) s)
        (fun st => .ret (finish st)) =
      Prog.tick^[indices.length] (.ret (finish (indices.foldl next s))) := by
  induction indices generalizing s with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldlM_cons, List.length_cons, Function.iterate_succ_apply']
    change Prog.tick (Prog.bind (Prog.bind (body i s) _) _) = _
    rw [hbody]
    exact congrArg Prog.tick (ih _)

private theorem loop_ticks {σ α : Type} (n : ℕ) (s : σ) (next : σ → ℕ → σ)
    (body : ℕ → σ → Prog ℝ σ) (finish : σ → α)
    (hbody : ∀ i st, body i st = .ret (next st i)) :
    Prog.bind (Prog.forLoop n s body) (fun st => .ret (finish st)) =
      Prog.tick^[n] (.ret (finish ((List.range n).foldl next s))) := by
  simpa [Prog.forLoop] using fold_ticks (List.range n) s next body finish hbody

private theorem run_ticks {α : Type} (S : Solver) (n : ℕ) (out : α) :
    run S (Prog.tick^[n] (.ret out)) = PMF.pure (out, n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change charge 1 (run S (Prog.tick^[n] (.ret out))) = _
    simp [ih, charge, PMF.pure_map]

/-- The interpreter records exactly `s` ticks for the published relabelling
pass. Looking up the same keys by traversing the list visits `s*(s+1)/2` cons
cells. The traversal count excludes all other work in the pass. -/
theorem relabel_costs (S : Solver) (sorted : List (ℕ × ℕ)) :
    run S (relabel sorted) = PMF.pure (literalRelabel sorted, sorted.length) ∧
      2 * (∑ i ∈ Finset.range sorted.length, (countedGetD (0, 0) sorted i).2) =
        sorted.length * (sorted.length + 1) := by
  constructor
  · rw [← run_ticks S sorted.length (literalRelabel sorted)]
    congr 1
    unfold relabel literalRelabel
    apply loop_ticks
    intro i st
    dsimp only
    rw [countedGetD_value]
    unfold assign
    cases st.1 with
    | none => rfl
    | some prev => by_cases he : (sorted.getD i (0, 0)).1 = prev <;> simp only [he, if_true, if_false]
  · calc
      _ = 2 * (∑ i ∈ Finset.range sorted.length, (i + 1)) := by
        congr 1
        exact Finset.sum_congr rfl fun i hi => visits_at_index _ _ _ (Finset.mem_range.mp hi)
      _ = _ := sum_visits _

#print axioms countedGetD_value
#print axioms relabel_costs

end Audit.ListLookup1352
