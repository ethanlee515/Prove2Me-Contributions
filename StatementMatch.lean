import DisproofD17
import Theorems.Thm_MatchIndiff_PublicSM_lemma_D_17
import Solutions.Sol_MatchIndiff_PublicSM_lemma_D_17

namespace MatchIndiff.PublicSM

-- This elaborates only if D17Statement is definitionally the type of the
-- published theorem. The published theorem body is an open `sorry` placeholder;
-- it is not used by not_D17Statement.
example : D17Statement := by
  exact @lemma_D_17

example : ¬ D17Statement := by
  exact solution

#print axioms solution

end MatchIndiff.PublicSM
