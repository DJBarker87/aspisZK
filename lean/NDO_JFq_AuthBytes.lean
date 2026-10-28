import NDO_JFq_Compare
import NDO_JFs_PrefixRead
import NDO_JFs_SuffixRead
import NDO_JFt_Index
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_AuthBytes
open Aeneas Aeneas.Std Result AspisR1Stage2

def proofHash : Array U8 32#usize := ⟨[85#u8,56#u8,108#u8,80#u8,125#u8,63#u8,238#u8,235#u8,252#u8,69#u8,39#u8,42#u8,28#u8,241#u8,92#u8,51#u8,204#u8,185#u8,204#u8,240#u8,168#u8,168#u8,244#u8,17#u8,128#u8,252#u8,101#u8,77#u8,128#u8,111#u8,255#u8,111#u8],rfl⟩
theorem proofHash_selected : (JFq_Range.segment 16 32 (by decide)).val=proofHash.val := by
  change (JFx_DataCheckpoint00.bytes.drop 16).take 32=proofHash.val
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms proofHash_selected

def publicHash : Array U8 32#usize := ⟨[246#u8,188#u8,212#u8,148#u8,70#u8,241#u8,7#u8,125#u8,44#u8,94#u8,212#u8,190#u8,148#u8,14#u8,145#u8,240#u8,190#u8,68#u8,78#u8,252#u8,90#u8,232#u8,48#u8,36#u8,236#u8,7#u8,0#u8,184#u8,194#u8,5#u8,195#u8,49#u8],rfl⟩
theorem publicHash_selected : (JFq_Range.segment 48 32 (by decide)).val=publicHash.val := by
  change (JFx_DataCheckpoint00.bytes.drop 48).take 32=publicHash.val
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms publicHash_selected

def checksum : Array U8 32#usize := ⟨[32#u8,246#u8,96#u8,198#u8,113#u8,134#u8,136#u8,76#u8,14#u8,247#u8,82#u8,65#u8,136#u8,220#u8,116#u8,122#u8,97#u8,205#u8,102#u8,170#u8,156#u8,68#u8,205#u8,19#u8,231#u8,251#u8,82#u8,170#u8,25#u8,168#u8,239#u8,199#u8],rfl⟩
theorem checksum_selected : (JFq_Range.segment 1736 32 (by decide)).val=checksum.val := by
  dsimp only [JFq_Range.segment,JFx_NativeBytes.checkpoint,JFx_NativeBytes.checkpointBytes]
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms checksum_selected

def magic : Array U8 8#usize := Array.make 8#usize
  [82#u8,49#u8,80#u8,50#u8,67#u8,75#u8,80#u8,50#u8]
def header : Slice U8 := ⟨magic.val,by rw [magic.property];scalar_tac⟩
theorem first16 : JFx_NativeBytes.checkpoint.val.take 16=
    [82#u8,49#u8,80#u8,50#u8,67#u8,75#u8,80#u8,50#u8,2#u8,10#u8,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8] := rfl

theorem prefix_read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
    JFx_NativeBytes.checkpoint {«end»:=8#usize}=ok header := by
  apply JFs_PrefixRead.source _ _ (by rw [show JFx_NativeBytes.checkpoint.length=1768 from JFx_NativeBytes.checkpointBytes_length];decide)
  rfl

theorem byte (i : Usize) (inside : i.val<16) (b : U8)
    (selected : ([82#u8,49#u8,80#u8,50#u8,67#u8,75#u8,80#u8,50#u8,2#u8,10#u8,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8] : List U8)[i.val]?=some b) :
    Slice.index_usize JFx_NativeBytes.checkpoint i=ok b := by
  apply JFt_Index.source _ _ (by rw [show JFx_NativeBytes.checkpoint.length=1768 from JFx_NativeBytes.checkpointBytes_length];omega) b
  have h:=congrArg (fun xs : List U8 => xs[i.val]?) first16
  rw [List.getElem?_take_of_lt inside] at h
  exact h.trans selected

#print axioms first16
#print axioms prefix_read
#print axioms byte
end AspisR1.JFq_AuthBytes
end
