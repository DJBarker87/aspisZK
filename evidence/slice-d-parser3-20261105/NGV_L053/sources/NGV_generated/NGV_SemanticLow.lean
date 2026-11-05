import NGV_SemanticCut
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_SemanticLow
open AspisS1NativeCompact NGV_RowPayload NGV_ByteWindow
/-- Original ordinary-row copy on arbitrary SAME output prestate. -/
theorem result (input before : Slice U8) (row : U8) (iter : NGV_SemanticCut.Iter)
 (src dst sourceEnd outputEnd size : Usize)
 (live : row.val<27) (low : row.val<14)
 (inputSize : input.val.length=7015) (outputSize : before.val.length=13831)
 (srcValue : src.val=NGD_SemanticSchedule.src row.val+5)
 (dstValue : dst.val=NGD_SemanticSchedule.dst row.val+5)
 (sizeValue : size.val=NFU_PacketDomains.payloadSize row.val)
 (sourceValue : sourceEnd.val=src.val+size.val)
 (outputValue : outputEnd.val=dst.val+size.val)
 (packet : Packet input before row.val) :
 NGV_SemanticCut.payload AspisS1ValuesOwnedInstallation.nativeValues input iter row
   (middle input before row.val) src dst size=
 ok (.cont (iter,after packet,sourceEnd,outputEnd)) := by
 have bounds:=NGD_SemanticSchedule.windows row.val live
 have stored : NGD_SemanticSchedule.stored row.val=NFU_PacketDomains.payloadSize row.val := by
   simp only [NGD_SemanticSchedule.stored,if_neg (by omega : ¬14≤row.val)]
 have middleSize : (middle input before row.val).val.length=13831 := by
   unfold middle;rw [write_length,outputSize]
 have sourceWidth : sourceEnd.val-src.val=NGD_SemanticSchedule.stored row.val := by omega
 have outputWidth : outputEnd.val-dst.val=NFU_PacketDomains.payloadSize row.val := by omega
 have sourceRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   input {start:=src,«end»:=sourceEnd}=ok (source input row.val) := by
   simpa only [sourceWidth,srcValue,source] using
    read input src sourceEnd (by constructor <;> omega)
 have targetRead : core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8)
   (middle input before row.val) {start:=dst,«end»:=outputEnd}=
   ok (target input before row.val,fun x=>write (middle input before row.val) dst.val x) := by
   simpa only [outputWidth,dstValue,target] using
    read_mut (middle input before row.val) dst outputEnd (by constructor <;> omega)
 have copyRun:=copy (target input before row.val) (source input row.val) (by
   obtain ⟨h1,h2⟩:=domains input before row.val live inputSize outputSize
   omega)
 have ordinary : compact.compact_row row=ok false := by
   simp [compact.compact_row,show ¬row≥14#u8 by scalar_tac]
 unfold NGV_SemanticCut.payload
 rw [ordinary]
 simp only [bind_tc_ok,Bool.false_eq_true,if_false]
 rw [NGV_SemanticArithmetic.add dst size outputEnd outputValue,targetRead]
 simp only [bind_tc_ok]
 change (src+size >>= _) = _
 rw [NGV_SemanticArithmetic.add src size sourceEnd sourceValue,bind_tc_ok,sourceRead,bind_tc_ok,copyRun,bind_tc_ok]
 unfold after
 rw [packet.low low,dstValue]
#print axioms result
end NGV_SemanticLow
