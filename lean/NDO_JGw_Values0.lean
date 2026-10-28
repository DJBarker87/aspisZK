import RPt_JFn_ArrayBuilder
import RPt_JFn_ValueBlock
import RPt_JFo_QueryIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value00_0
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [242#u8,103#u8,185#u8,78#u8,81#u8,206#u8,230#u8,111#u8,28#u8,251#u8,180#u8,75#u8,221#u8,225#u8,46#u8,18#u8,51#u8,97#u8,210#u8,60#u8,217#u8,83#u8,138#u8,54#u8,100#u8,252#u8,182#u8,35#u8,215#u8,84#u8,92#u8,108#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 1320773618#u32 1877397073#u32 1270151964#u32 305062365#u32 1020420403#u32 915035097#u32 599194724#u32 1817990359#u32

theorem selected : ((JFn_ValueBlock.value ⟨0,by decide⟩).val.drop 0).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 0 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=1320773618#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=1877397073#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1270151964#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=305062365#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=1020420403#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=915035097#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=599194724#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=1817990359#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 1320773618<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 1877397073<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1270151964<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 305062365<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 1020420403<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 915035097<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 599194724<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 1817990359<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem query : Array.index_usize JFo_Prepared.value.queries 0#usize=ok 93499#u32 :=
  JFo_QueryIndex.source _ _ (by decide) 93499#u32 rfl
#print axioms query

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨0,by decide⟩) 0#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 0#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value00_0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value00_1
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [212#u8,160#u8,54#u8,93#u8,74#u8,235#u8,231#u8,63#u8,20#u8,197#u8,138#u8,24#u8,238#u8,162#u8,46#u8,107#u8,69#u8,77#u8,33#u8,66#u8,4#u8,105#u8,128#u8,111#u8,164#u8,189#u8,246#u8,45#u8,205#u8,105#u8,52#u8,42#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 1563861204#u32 1072163658#u32 411747604#u32 1798218478#u32 1109478725#u32 1870686468#u32 771145124#u32 708078029#u32

theorem selected : ((JFn_ValueBlock.value ⟨0,by decide⟩).val.drop 32).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 32 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=1563861204#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=1072163658#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=411747604#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=1798218478#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=1109478725#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=1870686468#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=771145124#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=708078029#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 1563861204<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 1072163658<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 411747604<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 1798218478<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 1109478725<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 1870686468<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 771145124<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 708078029<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨0,by decide⟩) 1#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 1#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value00_1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value00_2
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [205#u8,141#u8,226#u8,60#u8,96#u8,255#u8,171#u8,13#u8,212#u8,194#u8,220#u8,70#u8,238#u8,166#u8,36#u8,117#u8,101#u8,123#u8,40#u8,63#u8,209#u8,142#u8,248#u8,26#u8,69#u8,144#u8,27#u8,15#u8,246#u8,142#u8,227#u8,58#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 1021480397#u32 229375840#u32 1188872916#u32 1965336302#u32 1059617637#u32 452497105#u32 253464645#u32 987991798#u32

theorem selected : ((JFn_ValueBlock.value ⟨0,by decide⟩).val.drop 64).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 64 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=1021480397#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=229375840#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1188872916#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=1965336302#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=1059617637#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=452497105#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=253464645#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=987991798#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 1021480397<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 229375840<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1188872916<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 1965336302<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 1059617637<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 452497105<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 253464645<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 987991798<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨0,by decide⟩) 2#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 2#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value00_2
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value00_3
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [174#u8,188#u8,180#u8,5#u8,245#u8,177#u8,5#u8,81#u8,19#u8,228#u8,77#u8,73#u8,201#u8,244#u8,246#u8,87#u8,77#u8,57#u8,17#u8,78#u8,123#u8,153#u8,30#u8,71#u8,65#u8,192#u8,250#u8,39#u8,116#u8,207#u8,168#u8,109#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 95730862#u32 1359327733#u32 1229841427#u32 1475802313#u32 1309751629#u32 1193187707#u32 670744641#u32 1839779700#u32

theorem selected : ((JFn_ValueBlock.value ⟨0,by decide⟩).val.drop 96).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 96 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=95730862#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=1359327733#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1229841427#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=1475802313#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=1309751629#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=1193187707#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=670744641#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=1839779700#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 95730862<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 1359327733<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1229841427<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 1475802313<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 1309751629<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 1193187707<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 670744641<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 1839779700<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨0,by decide⟩) 3#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 3#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value00_3
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Values0
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JGw_Value00_0.value,SAQ_RecordDecode.fromRecord JGw_Value00_1.value,SAQ_RecordDecode.fromRecord JGw_Value00_2.value,SAQ_RecordDecode.fromRecord JGw_Value00_3.value]
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨0,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨0,by decide⟩ _ _ _ _
    JGw_Value00_0.source JGw_Value00_1.source JGw_Value00_2.source JGw_Value00_3.source
#print axioms source
end AspisR1.JGw_Values0
end
