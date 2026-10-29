import R1Z.PV_OWNC_FlatMap
set_option autoImplicit false
namespace R1Z.PV_OWNC_PathPredicate
open PV_OWN_Link
/-- Exactly the source matches! predicate: all kind payloads remain intact. -/
def keep (v : Link) : Bool :=
 match v.kind with
 | .privatePathCurrent _ | .privatePathLeft _ | .privatePathRight _ => false
 | _ => true

theorem path_current (n : UInt8) (p c : UInt16) : keep ⟨.privatePathCurrent n,p,c⟩=false := rfl
theorem path_left (n : UInt8) (p c : UInt16) : keep ⟨.privatePathLeft n,p,c⟩=false := rfl
theorem path_right (n : UInt8) (p c : UInt16) : keep ⟨.privatePathRight n,p,c⟩=false := rfl
#print axioms path_current
#print axioms path_left
#print axioms path_right
end R1Z.PV_OWNC_PathPredicate
