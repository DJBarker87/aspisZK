import NJC_OrderedCalls
import NFS_QueryLoopRoot
set_option autoImplicit false
noncomputable section
namespace NJJ_QueryOps
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
/-- Every query operation is installed by name. No seed/dictionary parameter,
no default successful child, and no opaque payload slot. -/
def concrete : Port3_NativeQueryBody.Ops where
 op0 := OraclePortStdBuilder.fromFn
 op1 := fun q=>ok (Port4C_RowStd.fromK q)
 op2 := SAQ_Arithmetic.add
 op3 := SAQ_MixedSource.mulE
 op4 := ok 0#u32
 op5 := ok 1#u32
 op6 := AspisR1Qm31ArithmeticProbe.field.M31.sub
 op7 := AspisR1Qm31ArithmeticProbe.field.M31.mul
 op8 := S7Kani3BasisOuter.double
 op9 := SAQ_Arithmetic.mulK
 op10 := fun m=>ok (Port4C_RowStd.fromM m)
 op11 := Port4B_Opening.opening
 op12 := Slice.index_usize
 op13 := Array.index_usize
 op14 := Port3_NativeRowFrame.push
 op15 := fun _ _ _=>ok ()
 op16 := SAQ_LineQuery.line
 op17 := FIp_CircleQuery.circle
 op18 := Port5Q1_GeometryBinding.forQuery
 op19 := Port3_QueryStage.mark
 op20 := FIp_DotsAdapter.dots
 op21 := SAQ_Decoder.read
 widePartialEq := FIp_Equality.dictionary

def installed := NFS_QueryOps.installed concrete

/-- Complete concrete release selection at the parser, opening and observer
boundaries. The full record above fixes all other fields as well. -/
theorem fields :
 concrete.op11=Port4B_Opening.opening ∧ concrete.op21=SAQ_Decoder.read ∧
 concrete.op19=Port3_QueryStage.mark ∧ concrete.widePartialEq=FIp_Equality.dictionary :=
 ⟨rfl,rfl,rfl,rfl⟩

#print axioms fields
#print concrete
end NJJ_QueryOps
