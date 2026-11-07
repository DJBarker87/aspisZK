import NFS_PacketRoot
import Port3_QueryStage
set_option autoImplicit false
noncomputable section
namespace LIBC_QueryOps
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
/-- Literal concrete adopted source helpers, from IDb_Components.query.
No arbitrary or failing seed operation is used. -/
def seed : Port3_NativeQueryBody.Ops where
  op0 := OraclePortStdBuilder.fromFn
  op1 := fun q => ok (Port4C_RowStd.fromK q)
  op2 := SAQ_Arithmetic.add
  op3 := SAQ_MixedSource.mulE
  op4 := ok 0#u32
  op5 := ok 1#u32
  op6 := AspisR1Qm31ArithmeticProbe.field.M31.sub
  op7 := AspisR1Qm31ArithmeticProbe.field.M31.mul
  op8 := S7Kani3BasisOuter.double
  op9 := SAQ_Arithmetic.mulK
  op10 := fun m => ok (Port4C_RowStd.fromM m)
  op11 := Port4B_Opening.opening
  op12 := Slice.index_usize
  op13 := Array.index_usize
  op14 := Port3_NativeRowFrame.push
  op15 := fun _ _ _ => ok ()
  op16 := SAQ_LineQuery.line
  op17 := FIp_CircleQuery.circle
  op18 := Port5Q1_GeometryBinding.forQuery
  op19 := Port3_QueryStage.mark
  op20 := FIp_DotsAdapter.dots
  op21 := SAQ_Decoder.read
  widePartialEq := FIp_Equality.dictionary

def ops : Port3_NativeQueryBody.Ops := NFS_CallerDomains.ops seed
theorem closed_selection : ops = NFS_QueryOps.installed (NFS_CallerDomains.select seed) := rfl
theorem all_slots_fixed (other : Port3_NativeQueryBody.Ops) : NFS_CallerDomains.ops other=ops :=
 NFS_CallerDomains.no_seed other seed
#print axioms closed_selection
#print axioms all_slots_fixed
end LIBC_QueryOps
