import NNH_AdapterStd
set_option autoImplicit false
noncomputable section
namespace NNH_AdapterStdCorrect
open Aeneas Aeneas.Std AdapterRw
/-- Source trait fields at AdapterRwModel lines134–135: eq=op1, ne=op0.
The prior selection reversed these two TX1-only fields and is superseded. -/
def install (base : Ops) : Ops :=
 {NNH_AdapterStd.install base with
  op0:=fun inst left right=>Aeneas.Std.core.slice.cmp.PartialEqSlice.ne inst left right.to_slice
  op1:=fun inst left right=>Aeneas.Std.core.slice.cmp.PartialEqSlice.eq inst left right.to_slice}

theorem sliceArrayEq (base : Ops) {N : Usize} (left : Slice U8) (right : Array U8 N) :
 (Slice.Insts.CoreCmpPartialEqArray (install base) N core.cmp.PartialEqU8).eq left right=
 core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 left right.to_slice := rfl

theorem sliceArrayNe (base : Ops) {N : Usize} (left : Slice U8) (right : Array U8 N) :
 (Slice.Insts.CoreCmpPartialEqArray (install base) N core.cmp.PartialEqU8).ne left right=
 core.slice.cmp.PartialEqSlice.ne core.cmp.PartialEqU8 left right.to_slice := rfl
#print axioms sliceArrayEq
#print axioms sliceArrayNe
end NNH_AdapterStdCorrect
