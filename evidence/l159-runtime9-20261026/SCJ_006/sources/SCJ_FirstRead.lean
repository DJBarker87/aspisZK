import SCH_CollisionAppend
import SCH_EventKnownSuffix
set_option autoImplicit false
namespace AspisR1.SCJ_FirstRead
open FS AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]
/-- Erasing an INTERIOR query is valid if it was already cached with the
same answer at that point. This condition is stronger than sublist inclusion. -/
theorem cached_interior (bad : I → Table I A → A → Prop) (t : Table I A)
    (prior suffix : List (I × A)) (i : I) (answer : A)
    (cached : SCH_TableAfter.after t prior i = some answer) :
    hitsBad bad t (prior ++ (i,answer)::suffix) ↔
      hitsBad bad t (prior ++ suffix) := by
  have unchanged : put (SCH_TableAfter.after t prior) i answer =
      SCH_TableAfter.after t prior := by
    funext j
    by_cases same : j = i
    · subst j
      simp only [put,ite_true,cached]
    · simp only [put,if_neg same]
  rw [SCH_CollisionAppend.append,SCH_CollisionAppend.append]
  simp only [hitsBad,cached,Option.some_ne_none,false_and,false_or,unchanged]

#print axioms cached_interior
end AspisR1.SCJ_FirstRead
