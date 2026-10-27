import KSC1_FnState
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace KSC1.FnProbe

theorem add_value {x y z : Usize} (h : x.val + y.val = z.val) : x + y = ok z := by
  obtain ⟨r,hr,hv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=x) (y:=y) (by scalar_tac))
  have hz : r = z := UScalar.eq_of_val_eq (by omega)
  simpa only [hz] using hr
#print axioms add_value

def bump : core.ops.function.FnMut Nat Usize Nat :=
  {FnOnceInst := {call_once := fun c _ => ok c}, call_mut := fun c _ => ok (c,2*c)}
def stopping : core.ops.function.FnMut Nat Usize Nat :=
  {FnOnceInst := {call_once := fun c _ => ok c},
   call_mut := fun c i => if i.val = 2 then fail .panic else ok (c,2*c)}
def mapper : core.ops.function.FnMut (List Nat) Nat Nat :=
  {FnOnceInst := {call_once := fun _ x => ok (10*x)},
   call_mut := fun seen x => ok (10*x,seen ++ [x])}

theorem state_sequence :
    KSA_Isolated.core.array.fromFnList bump 4 0#usize 1 = ok ([1,2,4,8],16) := by
  have h01 : 0#usize + 1#usize = ok 1#usize := add_value rfl
  have h12 : 1#usize + 1#usize = ok 2#usize := add_value rfl
  have h23 : 2#usize + 1#usize = ok 3#usize := add_value rfl
  simp [KSA_Isolated.core.array.fromFnList, bump, h01, h12, h23]

theorem empty_state :
    KSA_Isolated.core.array.fromFnList stopping 0 0#usize 1 = ok ([],1) := by rfl

theorem panic_at_two :
    KSA_Isolated.core.array.fromFnList stopping 4 0#usize 1 = fail .panic := by
  have h01 : 0#usize + 1#usize = ok 1#usize := add_value rfl
  have h12 : 1#usize + 1#usize = ok 2#usize := add_value rfl
  simp [KSA_Isolated.core.array.fromFnList, stopping, h01, h12]

theorem state_array :
    (do let (a,s) ← KSA_Isolated.XRn_Join_fromFnState 4#usize bump 1
        ok (a.val,s)) = ok ([1,2,4,8],16) := by
  simp [KSA_Isolated.XRn_Join_fromFnState, state_sequence]

theorem from_fn_array :
    (do let a ← KSA_Isolated.core.array.from_fn 4#usize bump 1
        ok a.val) = ok [1,2,4,8] := by
  simp [KSA_Isolated.core.array.from_fn, state_sequence]

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
