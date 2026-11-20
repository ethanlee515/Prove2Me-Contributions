import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model
import Definitions.Def_MatchIndiff_PublicSM_Tape

namespace MatchIndiff.PublicSM

/-- The proposition in the published `lemma_D_17` declaration. -/
def D17Statement : Prop :=
  ∀ {n m : ℕ} (Q : Fin m → Fin n → ℕ) (P : Fin n → Fin m → ℕ)
    (_hQ : ∀ h, IsRow (Q h)) (_hP : ∀ i, IsRow (P i)) (proc : Procedure n m),
    (∀ board : List Bool, (∀ d, tapeCheck Q proc d (P d) board = true) →
      maskE Q (board.take (pubPairs Q).length) = trueE Q P ∧
        ∃ ans, replay (proc (trueE Q P)) [] (board.drop (pubPairs Q).length) = some ans ∧
          IsTrueRun proc (trueE Q P) P ans) ∧
    (∀ ans : List Ans, IsTrueRun proc (trueE Q P) P ans →
      ans.length ≤ (Finset.univ.filter (fun x : Fin n × Fin m => trueE Q P x.1 x.2 = true)).card →
      ∃ board : List Bool, (∀ d, tapeCheck Q proc d (P d) board = true) ∧
        board.length ≤ mQ Q + 2 * (Finset.univ.filter
          (fun x : Fin n × Fin m => trueE Q P x.1 x.2 = true)).card)

/-- The empty market accepts every board locally, but an immediately stopping
procedure rejects the unused one-bit tape. -/
theorem not_D17Statement : ¬ D17Statement := by
  intro claim
  let Q : Fin 0 → Fin 0 → ℕ := fun _ _ => 0
  let P : Fin 0 → Fin 0 → ℕ := fun _ _ => 0
  let stop : Procedure 0 0 := fun _ _ => none
  have validQ : ∀ h, IsRow (Q h) := fun h => Fin.elim0 h
  have validP : ∀ d, IsRow (P d) := fun d => Fin.elim0 d
  have accept : ∀ d, tapeCheck Q stop d (P d) [true] = true :=
    fun d => Fin.elim0 d
  obtain ⟨ans, replayed, _⟩ := ((claim Q P validQ validP stop).1 [true] accept).2
  have rejected : replay (stop (trueE Q P)) []
      ([true].drop (pubPairs Q).length) = none := by
    simp [stop, pubPairs, replay]
  have impossible : (none : Option (List Ans)) = some ans :=
    rejected.symm.trans replayed
  cases impossible

#print axioms not_D17Statement

end MatchIndiff.PublicSM
