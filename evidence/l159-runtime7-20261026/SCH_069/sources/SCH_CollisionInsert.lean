import SCH_CollisionAppend
import SCH_TableFixed
set_option autoImplicit false
namespace AspisR1.SCH_CollisionInsert
open FS AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]

theorem table_append (t : Table I A) (left right : List (I × A)) :
    SCH_TableAfter.after t (left ++ right) = SCH_TableAfter.after (SCH_TableAfter.after t left) right := by
  induction left generalizing t with
  | nil => rfl
  | cons q rest ih => exact ih (put t q.1 q.2)

/-- A consistent cached replay can be erased in the MIDDLE of the charged
recorder without changing any later first-read collision test. -/
theorem same (bad : I → Table I A → A → Prop) (t : Table I A)
    (prior cached tail : List (I × A))
    (answers : ∀ q ∈ cached, SCH_TableAfter.after t prior q.1 = some q.2) :
    hitsBad bad t (prior ++ cached ++ tail) ↔ hitsBad bad t (prior ++ tail) := by
  have noNew := SCH_CollisionAppend.cached bad (SCH_TableAfter.after t prior) cached
    (fun q member => by rw [answers q member]; exact Option.some_ne_none _)
  have fixed := SCH_TableFixed.after_same (SCH_TableAfter.after t prior) cached answers
  rw [List.append_assoc,SCH_CollisionAppend.append,SCH_CollisionAppend.append]
  rw [SCH_CollisionAppend.append,noNew,false_or,fixed]

#print axioms table_append
#print axioms same
end AspisR1.SCH_CollisionInsert
