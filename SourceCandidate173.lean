-- Candidate disproof for submission 173, Lemma D.17. Mathematical derivation
-- checked by inspection. This file has not been run through the Lean kernel.
-- Prove2Me: https://prove2.me/theorems/4cc55ca0-e623-46d7-895b-1626a0b94d38
-- Expected: Lean 4.33.1, Mathlib 0df444a, Prove2Me's Model and Tape modules.
import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model
import Definitions.Def_MatchIndiff_PublicSM_Tape

namespace MatchIndiff.PublicSM

-- Exact binders and conclusion copied from the published declaration.
private def publishedD17 : Prop :=
  ∀ {n m : ℕ} (Q : Fin m → Fin n → ℕ) (P : Fin n → Fin m → ℕ)
    (hQ : ∀ h, IsRow (Q h)) (hP : ∀ i, IsRow (P i)) (proc : Procedure n m),
    (∀ board : List Bool, (∀ d, tapeCheck Q proc d (P d) board = true) →
      maskE Q (board.take (pubPairs Q).length) = trueE Q P ∧
        ∃ ans, replay (proc (trueE Q P)) [] (board.drop (pubPairs Q).length) = some ans ∧
          IsTrueRun proc (trueE Q P) P ans) ∧
    (∀ ans : List Ans, IsTrueRun proc (trueE Q P) P ans →
      ans.length ≤ (Finset.univ.filter (fun x : Fin n × Fin m => trueE Q P x.1 x.2 = true)).card →
      ∃ board : List Bool, (∀ d, tapeCheck Q proc d (P d) board = true) ∧
        board.length ≤ mQ Q + 2 * (Finset.univ.filter
          (fun x : Fin n × Fin m => trueE Q P x.1 x.2 = true)).card)

example : ¬ publishedD17 := by
  intro claim
  let Q : Fin 0 → Fin 0 → ℕ := fun _ _ => 0
  let P : Fin 0 → Fin 0 → ℕ := fun _ _ => 0
  let stop : Procedure 0 0 := fun _ _ => none
  have validQ : ∀ h, IsRow (Q h) := fun h => Fin.elim0 h
  have validP : ∀ d, IsRow (P d) := fun d => Fin.elim0 d
  have accept : ∀ d, tapeCheck Q stop d (P d) [true] = true := fun d => Fin.elim0 d
  obtain ⟨ans, replayed, _⟩ := ((claim Q P validQ validP stop).1 [true] accept).2
  have rejected : replay (stop (trueE Q P)) [] ([true].drop (pubPairs Q).length) = none := by
    simp [stop, pubPairs, replay]
  have impossible : (none : Option (List Ans)) = some ans := rejected.symm.trans replayed
  cases impossible

end MatchIndiff.PublicSM
