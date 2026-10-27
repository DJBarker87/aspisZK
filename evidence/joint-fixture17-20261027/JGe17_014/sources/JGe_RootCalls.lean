import JGe_Roots
import JFr_PrefixRecords
import JFw_Record
set_option autoImplicit false
namespace AspisR1.JGe_RootCalls
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes

theorem record (pre : r1_wire.Prefix) (records : pre.records.val=JFw_Records.frames) :
    r1_wire.Prefix.record pre 2#u8=ok (.Ok JFw_NativeRow02.record) := by
  have index : Array.index_usize pre.records 2#usize=ok JFw_NativeRow02.record := by
    simp only [Array.index_usize,Array.getElem?_Usize_eq,records]
    rfl
  change (do let s ← Array.index_usize pre.records 2#usize
             ok (core.result.Result.Ok s : core.result.Result (Slice U8) r1_wire.Error))=_
  rw [index,bind_tc_ok]
#print axioms record

theorem payload (pre : r1_wire.Prefix) (records : pre.records.val=JFw_Records.frames) :
    FinishModel.payload pre 2#u8=ok (.Ok (Array.to_slice JFq_Root1.value)) := by
  rw [FinishModel.payload,record pre records]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    Slice.index_SliceIndexRangeFromUsizeSliceInst]
  unfold core.slice.index.SliceIndexRangeFromUsizeSlice.index
  rw [if_pos (by change 5≤5+JFw_NativeRow02.payload.length;omega)]
  change ok (.Ok JFw_NativeRow02.payload)=_
  rw [JGe_Roots.payload]
#print axioms payload
end AspisR1.JGe_RootCalls
