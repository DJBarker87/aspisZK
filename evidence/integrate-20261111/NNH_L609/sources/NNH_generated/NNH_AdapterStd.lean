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

/-- Original standard slice methods, including their owned-update callbacks.
These are source-model selections, not new native std certificates. -/
def install (base : Ops) : Ops :=
 {base with
  op0:=fun inst left right=>Aeneas.Std.core.slice.cmp.PartialEqSlice.eq inst left right.to_slice
  op1:=fun inst left right=>Aeneas.Std.core.slice.cmp.PartialEqSlice.ne inst left right.to_slice
  op2:=optionEq
  op3:=fun {T} => (core.slice.index.SliceIndexRangeFullSlice T).index_mut
  op4:=fun {T} => (core.slice.index.SliceIndexRangeFullSlice T).index
  op5:=fun {T} => (core.slice.index.SliceIndexRangeFullSlice T).get_unchecked_mut
  op6:=fun {T} => (core.slice.index.SliceIndexRangeFullSlice T).get_unchecked
  op7:=fun {T} => (core.slice.index.SliceIndexRangeFullSlice T).get_mut
  op8:=fun {T} => (core.slice.index.SliceIndexRangeFullSlice T).get}

theorem option_selected (base : Ops) : @(install base).op2=@optionEq := rfl
#print axioms option_selected
end NNH_AdapterStd
