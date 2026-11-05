import NGV_SemanticCut
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_SemanticHigh
open AspisS1NativeCompact NGV_RowPayload NGV_ByteWindow
/-- Original expanded-row callee call on arbitrary SAME output prestate. -/
theorem result (input before : Slice U8) (row : U8) (iter : NGV_SemanticCut.Iter)
 (src dst sourceEnd outputEnd size half : Usize)
 (live : row.val<27) (high : 14≤row.val)
 (inputSize : input.val.length=7015) (outputSize : before.val.length=13831)
 (srcValue : src.val=NGD_SemanticSchedule.src row.val+5)
 (dstValue : dst.val=NGD_SemanticSchedule.dst row.val+5)
 (sizeValue : size.val=NFU_PacketDomains.payloadSize row.val)
 (halfValue : half.val=NGD_SemanticSchedule.stored row.val)
 (division : size/2#usize=ok half)
 (sourceValue : sourceEnd.val=src.val+half.val)
 (outputValue : outputEnd.val=dst.val+size.val)
 (packet : Packet input before row.val) :
 NGV_SemanticCut.payload AspisS1ValuesOwnedInstallation.nativeValues input iter row
   (middle input before row.val) src dst size=
 ok (.cont (iter,after packet,sourceEnd,outputEnd)) := by
 have bounds:=NGD_SemanticSchedule.windows row.val live
 have middleSize : (middle input before row.val).val.length=13831 := by
   unfold middle;rw [write_length,outputSize]
 have sourceWidth : sourceEnd.val-src.val=NGD_SemanticSchedule.stored row.val := by omega
 have outputWidth : outputEnd.val-dst.val=NFU_PacketDomains.payloadSize row.val := by omega
 have sourceRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   input {start:=src,«end»:=sourceEnd}=ok (source input row.val) := by
   have h:=read input src sourceEnd (by constructor <;> omega)
   rw [sourceWidth] at h
   simpa only [srcValue,source] using h
 have targetRead : core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8)
   (middle input before row.val) {start:=dst,«end»:=outputEnd}=
   ok (target input before row.val,fun x=>write (middle input before row.val) dst.val x) := by
   have h:=read_mut (middle input before row.val) dst outputEnd (by constructor <;> omega)
   rw [outputWidth] at h
   simpa only [dstValue,target] using h
 have compacted : compact.compact_row row=ok true := by
   simp [compact.compact_row,show row≥14#u8 by scalar_tac]
 unfold NGV_SemanticCut.payload
 rw [compacted]
 simp only [bind_tc_ok,if_true]
 rw [division,bind_tc_ok,NGV_SemanticArithmetic.add src half sourceEnd sourceValue,
   bind_tc_ok,sourceRead,bind_tc_ok,NGV_SemanticArithmetic.add dst size outputEnd outputValue,
   bind_tc_ok,targetRead]
 simp only [bind_tc_ok]
 change (AspisS1ValuesOwnedInstallation.expandValues (source input row.val) (target input before row.val) >>= _) = _
 rw [packet.adopted high]
 simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
 change (src+half >>= _) = _
 rw [NGV_SemanticArithmetic.add src half sourceEnd sourceValue,bind_tc_ok]
 unfold after
 rw [dstValue]
#print axioms result
end NGV_SemanticHigh
