import SCH_CollisionInventory
set_option autoImplicit false
namespace AspisR1.SCH_TableAfter
open FS AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]

def after : Table I A → List (I × A) → Table I A
  | t,[] => t
  | t,(i,a)::rest => after (put t i a) rest

theorem put_keeps (t : Table I A) (i j : I) (a : A) (known : t j ≠ none) :
    put t i a j ≠ none := by
  by_cases same : j=i
  · simp only [put,if_pos same,ne_eq,Option.some_ne_none,not_false_eq_true]
  · simpa only [put,if_neg same] using known

theorem keeps (t : Table I A) (tr : List (I × A)) (j : I) (known : t j ≠ none) :
    after t tr j ≠ none := by
  induction tr generalizing t with
  | nil => exact known
  | cons q rest ih => exact ih (put t q.1 q.2) (put_keeps t q.1 j q.2 known)

theorem read (t : Table I A) (tr : List (I × A)) (j : I)
    (member : j ∈ tr.map Prod.fst) : after t tr j ≠ none := by
  induction tr generalizing t with
  | nil => cases member
  | cons q rest ih =>
    rcases List.mem_cons.mp member with same | tail
    · subst j
      exact keeps _ rest q.1 (by simp only [put,if_pos rfl,ne_eq,Option.some_ne_none,not_false_eq_true])
    · exact ih (put t q.1 q.2) tail

#print axioms put_keeps
#print axioms keeps
#print axioms read
end AspisR1.SCH_TableAfter
