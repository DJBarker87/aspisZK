import NNH_Tx2SourceConfiguration
set_option autoImplicit false
noncomputable section
namespace NNH_AdapterStd
open Aeneas Aeneas.Std AdapterRw

/-- The Option equality method preserves the callee's Result and short-circuit
shape. It does not replace or inspect a function-pointer value. -/
def optionEq {T : Type} (inst : core.cmp.PartialEq T T) (left right : Option T) : Result Bool :=
 match left,right with
 | none,none => .ok true
 | some x,some y => inst.eq x y
 | _,_ => .ok false

/-- Full-range slice semantics, including the original slice in each update callback.
These are source-model selections, not new native std certificates. -/
def install (base : Ops) : Ops :=
 {base with
  op0:=fun inst left right=>Aeneas.Std.core.slice.cmp.PartialEqSlice.eq inst left right.to_slice
  op1:=fun inst left right=>Aeneas.Std.core.slice.cmp.PartialEqSlice.ne inst left right.to_slice
  op2:=optionEq
  op3:=fun _ slice=>.ok (slice,id)
  op4:=fun _ slice=>.ok slice
  op5:=fun _ ptr=>.ok ptr
  op6:=fun _ ptr=>.ok ptr
  op7:=fun _ slice=>.ok (some slice,fun out=>out.getD slice)
  op8:=fun _ slice=>.ok (some slice)}

theorem option_selected (base : Ops) : @(install base).op2=@optionEq := rfl
#print axioms option_selected
end NNH_AdapterStd
