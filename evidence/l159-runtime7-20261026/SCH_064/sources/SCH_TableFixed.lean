import SCH_TableAfter
set_option autoImplicit false
namespace AspisR1.SCH_TableFixed
open AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]

theorem put_same (t : Table I A) (i : I) (a : A) (same : t i = some a) : put t i a = t := by
  funext j
  by_cases equal : j=i
  · subst j; simp only [put,if_pos rfl,same]
  · simp only [put,if_neg equal]

theorem after_same (t : Table I A) (tr : List (I × A))
    (same : ∀ q ∈ tr, t q.1 = some q.2) : SCH_TableAfter.after t tr = t := by
  induction tr with
  | nil => rfl
  | cons q rest ih =>
    have first := same q List.mem_cons_self
    simp only [SCH_TableAfter.after,put_same t q.1 q.2 first]
    exact ih (fun r member => same r (List.mem_cons_of_mem _ member))

#print axioms put_same
#print axioms after_same
end AspisR1.SCH_TableFixed
