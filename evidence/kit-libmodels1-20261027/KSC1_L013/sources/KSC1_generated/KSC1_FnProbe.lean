import KSC1_FnState
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace KSC1.FnProbe

def bump : core.ops.function.FnMut Nat Usize Nat :=
  {FnOnceInst := {call_once := fun c _ => ok c}, call_mut := fun c _ => ok (c,2*c)}
def stopping : core.ops.function.FnMut Nat Usize Nat :=
  {FnOnceInst := {call_once := fun c _ => ok c},
   call_mut := fun c i => if i.val = 2 then fail .panic else ok (c,2*c)}
def mapper : core.ops.function.FnMut (List Nat) Nat Nat :=
  {FnOnceInst := {call_once := fun _ x => ok (10*x)},
   call_mut := fun seen x => ok (10*x,seen ++ [x])}

theorem state_sequence :
    KSA_Isolated.core.array.fromFnList bump 4 0#usize 1 = ok ([1,2,4,8],16) := by rfl

theorem empty_state :
    KSA_Isolated.core.array.fromFnList stopping 0 0#usize 1 = ok ([],1) := by rfl

theorem panic_at_two :
    KSA_Isolated.core.array.fromFnList stopping 4 0#usize 1 = fail .panic := by rfl

theorem state_array :
    (do let (a,s) ← KSA_Isolated.XRn_Join_fromFnState 4#usize bump 1
        ok (a.val,s)) = ok ([1,2,4,8],16) := by rfl

theorem from_fn_array :
    (do let a ← KSA_Isolated.core.array.from_fn 4#usize bump 1
        ok a.val) = ok [1,2,4,8] := by rfl

theorem map_sequence :
    (do let (a,s) ← KSA_Isolated.core.array.mapListFnMut mapper [1,2,3] []
        ok (a.val,s)) = ok ([10,20,30],[1,2,3]) := by rfl

#print axioms state_sequence
#print axioms empty_state
#print axioms panic_at_two
#print axioms state_array
#print axioms from_fn_array
#print axioms map_sequence
end KSC1.FnProbe
