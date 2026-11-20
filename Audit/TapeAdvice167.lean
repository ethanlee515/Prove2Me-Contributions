import Definitions.Def_HypRecov_SketchGuarantee

/-! # Paper 167, Theorem 1.1

The coin-length field of a linear sketch can encode membership in any set of
input sizes. A single finite machine reads the four ordinary parameter fields
and returns the marker that follows them.
-/

namespace Audit.TapeAdvice167

open HypRecov Turing

/-- Labels 0 through 3 skip one self-delimiting parameter each. Label 4 reads
the coin-list marker, clears the remaining zero or two bits, and returns it. -/
private def readerTM : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Fin 5
  main := 0
  σ := Bool
  initialState := false
  m stage :=
    let readMarker := fun (_ : Bool) (b : Option Bool) => b.getD false
    if stage = 4 then
      .pop () readMarker (.pop () (fun b _ => b) (.pop () (fun b _ => b)
        (.push () id (.load (fun _ => false) .halt))))
    else
      .pop () readMarker (.branch id
        (.pop () (fun _ _ => false) (.goto fun _ => stage))
        (.goto fun _ => stage + 1))

private def reader : TM2ComputableAux Bool Bool :=
  ⟨readerTM, Equiv.refl Bool, Equiv.refl Bool⟩

private def config (stage : Fin 5) (input : List Bool) : readerTM.Cfg :=
  ⟨some stage, false, fun _ => input⟩

private def advance (state : Option readerTM.Cfg) := state.bind readerTM.step

private theorem skip_field (i : Fin 5) (hi : i ≠ 4) (bits rest : List Bool) :
    advance^[bits.length + 1] (some (config i (encBits bits ++ rest))) =
      some (config (i + 1) rest) := by
  induction bits with
  | nil =>
    change readerTM.step (config i (false :: rest)) = _
    fin_cases i <;> first | exact (hi rfl).elim | rfl
  | cons b bs ih =>
    change advance^[(bs.length + 1) + 1]
      (some (config i (true :: b :: (encBits bs ++ rest)))) = _
    rw [Function.iterate_succ_apply]
    have popPair : advance (some (config i (true :: b :: (encBits bs ++ rest)))) =
        some (config i (encBits bs ++ rest)) := by
      fin_cases i <;> first | exact (hi rfl).elim | rfl
    rw [popPair]
    exact ih

private def suffix (bit : Bool) : List Bool :=
  if bit then [true, false, false] else [false]

private theorem reader_runs (n r k m : ℕ) (bit : Bool) :
    SpikyCVP.RunsWithin reader (encParams n r k m ++ suffix bit) [bit]
      (n.bits.length + r.bits.length + k.bits.length + m.bits.length + 5) := by
  let steps := 1 + ((m.bits.length + 1) + ((k.bits.length + 1) +
    ((r.bits.length + 1) + (n.bits.length + 1))))
  refine ⟨⟨⟨steps, ?_⟩, by dsimp [steps]; omega⟩⟩
  change advance^[steps] (some (config 0 ((encParams n r k m ++ suffix bit).map id))) =
    some (haltList readerTM [bit])
  rw [List.map_id]
  simp only [encParams, encNat, List.append_assoc]
  rw [Function.iterate_add_apply advance 1, Function.iterate_add_apply advance (m.bits.length + 1),
    Function.iterate_add_apply advance (k.bits.length + 1),
    Function.iterate_add_apply advance (r.bits.length + 1),
    skip_field 0 (by decide), show (0 : Fin 5) + 1 = 1 by decide,
    skip_field 1 (by decide), show (1 : Fin 5) + 1 = 2 by decide,
    skip_field 2 (by decide), show (2 : Fin 5) + 1 = 3 by decide,
    skip_field 3 (by decide)]
  cases bit <;> rfl

open Classical in
/-- The machines are fixed for every choice of `H`. Only the coin length
depends on membership. Every draw from the one-symbol alphabet is zero. -/
noncomputable def advisedSketch (H : Set ℕ) : LinearSketch where
  init := reader
  upd := default
  sub := default
  dec := default
  N n _ _ _ := if n ∈ H then 1 else 0
  M _ _ _ _ := 1

open Classical in
private theorem initializer_input (H : Set ℕ) (n r k m : ℕ)
    (ω : Fin ((advisedSketch H).N n r k m) → Fin ((advisedSketch H).M n r k m)) :
    encInit n r k m (coinList ω) = encParams n r k m ++ suffix (decide (n ∈ H)) := by
  have zeros : (fun i => (ω i).val) = fun _ => 0 := by
    funext i
    exact Nat.lt_one_iff.mp (ω i).isLt
  unfold coinList
  rw [zeros, List.ofFn_const]
  by_cases h : n ∈ H <;> simp [advisedSketch, h, suffix, encInit, encNat, encBits]

open Classical in
/-- On *every* possible draw the initializer outputs the advice bit. Its time
is at most the total number of binary parameter digits plus five machine steps. -/
theorem initializer_reads_membership (H : Set ℕ) (n r k m : ℕ)
    (ω : Fin ((advisedSketch H).N n r k m) → Fin ((advisedSketch H).M n r k m)) :
    SpikyCVP.RunsWithin (advisedSketch H).init (encInit n r k m (coinList ω)) [decide (n ∈ H)]
      (n.bits.length + r.bits.length + k.bits.length + m.bits.length + 5) := by
  rw [initializer_input H n r k m ω]
  exact reader_runs n r k m _

private theorem step_space (a b : readerTM.Cfg) (h : readerTM.step a = some b) :
    (b.stk ()).length ≤ max 1 (a.stk ()).length := by
  rcases a with ⟨label, reg, stack⟩
  cases label with
  | none => cases h
  | some stage =>
    have next : TM2.stepAux (readerTM.m stage) reg stack = b := Option.some.inj h
    subst b
    change Fin 5 at stage
    change Unit → List Bool at stack
    by_cases h4 : stage = 4
    · subst stage
      change ((stack ()).head?.getD false :: (stack ()).tail.tail.tail).length ≤
        max 1 (stack ()).length
      simp only [List.length_cons, List.length_tail]
      omega
    · change ((TM2.stepAux (readerTM.m stage) reg stack).stk ()).length ≤ max 1 (stack ()).length
      simp only [readerTM, if_neg h4, TM2.stepAux, id_eq]
      cases (stack ()).head?.getD false
      · change (stack ()).tail.length ≤ _
        simp only [List.length_tail]
        omega
      · change (stack ()).tail.tail.length ≤ _
        simp only [List.length_tail]
        omega

private theorem reader_space (input : List Bool) :
    SpaceWithin reader input (max 1 input.length) := by
  intro cfg reach
  change (∑ k : Unit, (cfg.stk k).length) ≤ max 1 input.length
  rw [Fintype.sum_unique]
  induction reach with
  | refl =>
    change (input.map id).length ≤ max 1 input.length
    simp
  | tail _ h ih => exact (step_space _ _ h).trans (max_le (le_max_left _ _) ih)

open Classical in
/-- At every reachable configuration, all stacks together use at most three
bits beyond the ordinary parameter encoding. -/
theorem initializer_space (H : Set ℕ) (n r k m : ℕ)
    (ω : Fin ((advisedSketch H).N n r k m) → Fin ((advisedSketch H).M n r k m)) :
    SpaceWithin (advisedSketch H).init (encInit n r k m (coinList ω))
      ((encParams n r k m).length + 3) := by
  rw [initializer_input H n r k m ω]
  intro cfg reach
  apply (reader_space _ cfg reach).trans
  cases h : decide (n ∈ H) <;> simp [suffix]

/-- Size `encode c + 2` selects one coin exactly when program `c` halts on input zero. -/
def haltingSizes : Set ℕ :=
  {n | 2 ≤ n ∧ ((Denumerable.ofNat Nat.Partrec.Code (n - 2)).eval 0).Dom}

/-- Even restricted to `n ≥ 2`, `r = k = 2`, and the budget `η = 1/8`
(`m = 8`), the sketch's coin length can be uncomputable. -/
theorem halting_tape_length_not_computable :
    ¬ Computable (fun t : ℕ => (advisedSketch haltingSizes).N (t + 2) 2 2 8) := by
  classical
  intro h
  apply ComputablePred.halting_problem 0
  refine ⟨Classical.decPred _, ?_⟩
  have compares := Primrec.beq.to_comp.comp (h.comp (Computable.encode (α := Nat.Partrec.Code))) (Computable.const 1)
  apply compares.of_eq
  intro c
  by_cases halts : (c.eval 0).Dom <;>
    simp [advisedSketch, haltingSizes, halts]

#print axioms halting_tape_length_not_computable
#print axioms initializer_reads_membership
#print axioms initializer_space

end Audit.TapeAdvice167
