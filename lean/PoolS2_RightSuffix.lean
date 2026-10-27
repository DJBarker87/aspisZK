import PoolS2_RightStep
set_option autoImplicit false
namespace AspisR1.PoolS2_RightSuffix
open Aeneas Aeneas.Std Result PoolS2_RightStep

def remaining (keys : Slice Key) (root : Key) (right : Nat) (unique : Bool) : Bool :=
  unique && (keys.val.drop right).all (fun other => decide (root.val ≠ other.val))

theorem next (keys : Slice Key) (root : Key) (right : Nat) (unique : Bool)
    (within : right < keys.val.length) :
    remaining keys root right unique = remaining keys root (right+1)
      (unique && decide (root.val ≠ (keys.val[right]).val)) := by
  simp only [remaining,List.drop_eq_getElem_cons within,List.all_cons,Bool.and_assoc]

theorem ended (keys : Slice Key) (root : Key) (right : Nat) (unique : Bool)
    (outside : keys.val.length ≤ right) : remaining keys root right unique = unique := by
  simp [remaining,List.drop_eq_nil_of_le outside]

#print axioms next
#print axioms ended
end AspisR1.PoolS2_RightSuffix
