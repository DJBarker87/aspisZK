import PoolS2_RightExact
set_option autoImplicit false
namespace AspisR1.PoolS2_UniqueSuffix
open Aeneas Aeneas.Std Result PoolS2_RightStep

abbrev allDifferent (keys : List Key) : Prop :=
  keys.Pairwise (fun a b => a.val ≠ b.val)

def remaining (keys : Slice Key) (left : Nat) (unique : Bool) : Bool :=
  unique && decide (allDifferent (keys.val.drop left))

theorem row_decide (root : Key) (rest : List Key) :
    rest.all (fun other => decide (root.val ≠ other.val)) =
      decide (∀ other ∈ rest, root.val ≠ other.val) := by
  induction rest with
  | nil => simp
  | cons other rest ih =>
    rw [List.all_cons,ih]
    simp

theorem next (keys : Slice Key) (left : Nat) (unique : Bool)
    (within : left < keys.val.length) :
    remaining keys left unique = remaining keys (left+1)
      (unique && (keys.val.drop (left+1)).all
        (fun other => decide ((keys.val[left]).val ≠ other.val))) := by
  simp only [remaining,List.drop_eq_getElem_cons within,allDifferent,List.pairwise_cons]
  rw [row_decide]
  simp [Bool.and_assoc]

theorem ended (keys : Slice Key) (left : Nat) (unique : Bool)
    (outside : keys.val.length ≤ left) : remaining keys left unique = unique := by
  simp [remaining,allDifferent,List.drop_eq_nil_of_le outside]

#print axioms row_decide
#print axioms next
#print axioms ended
end AspisR1.PoolS2_UniqueSuffix
