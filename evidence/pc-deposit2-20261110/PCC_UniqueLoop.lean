import PCC_BasicReferences
set_option autoImplicit false
namespace PCC
open PCA
/-- Boolean recurrence matching source-order pair comparisons. Native work
must cover ONE inner-loop comparison on arbitrary pre-state, then this fold. -/
def uniqueKeys : List Bytes → Bool
  | [] => true
  | x::xs => xs.all (fun y => x != y) && uniqueKeys xs

theorem unique_keys_iff (xs : List Bytes) :
    uniqueKeys xs = true ↔ xs.Pairwise (· ≠ ·) := by
  induction xs with
  | nil => simp [uniqueKeys]
  | cons x xs ih => simp [uniqueKeys,List.pairwise_cons,ih]
#print axioms unique_keys_iff
end PCC
