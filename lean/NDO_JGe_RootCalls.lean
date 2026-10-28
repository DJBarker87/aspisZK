import NDO_JGe_Roots
import NDO_JFr_PrefixRecords
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
  unfold r1_wire.Prefix.record
  simp only [if_neg (by decide : ¬ (2#u8 ≥ 27#u8)),lift,bind_tc_ok]
  have cast : UScalar.cast .Usize 2#u8=2#usize := by scalar_tac
  rw [cast]
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
  have length : JFw_NativeRow02.record.length=37 := by
    have pl : JFw_NativeRow02.payload.val.length=32 := JFw_NativeRow02.payload_length
    simp only [JFw_NativeRow02.record,JFw_Frames.frame,Slice.length,List.length_cons,pl]
  rw [if_pos (by change 5≤JFw_NativeRow02.record.length;rw [length];decide)]
  change ok (core.result.Result.Ok JFw_NativeRow02.payload : core.result.Result (Slice U8) r1_wire.Error)=_
  rw [JGe_Roots.payload]
#print axioms payload
end AspisR1.JGe_RootCalls
