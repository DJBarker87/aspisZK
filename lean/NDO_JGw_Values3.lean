import RPt_JFn_ArrayBuilder
import RPt_JFn_ValueBlock
import RPt_JFo_QueryIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value03_0
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [255#u8,165#u8,161#u8,98#u8,105#u8,72#u8,33#u8,106#u8,245#u8,218#u8,70#u8,68#u8,56#u8,96#u8,216#u8,48#u8,160#u8,103#u8,156#u8,28#u8,107#u8,6#u8,225#u8,99#u8,244#u8,177#u8,171#u8,79#u8,92#u8,197#u8,54#u8,111#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 1654760959#u32 1780566121#u32 1145494261#u32 819486776#u32 480012192#u32 1675691627#u32 1336652276#u32 1865860444#u32

theorem selected : ((JFn_ValueBlock.value ⟨3,by decide⟩).val.drop 0).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 0 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=1654760959#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=1780566121#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1145494261#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=819486776#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=480012192#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=1675691627#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=1336652276#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=1865860444#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 1654760959<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 1780566121<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1145494261<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 819486776<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 480012192<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 1675691627<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 1336652276<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 1865860444<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem query : Array.index_usize JFo_Prepared.value.queries 3#usize=ok 245899#u32 :=
  JFo_QueryIndex.source _ _ (by decide) 245899#u32 rfl
#print axioms query

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨3,by decide⟩) 0#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 0#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value03_0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value03_1
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [172#u8,71#u8,254#u8,62#u8,239#u8,164#u8,62#u8,99#u8,18#u8,249#u8,204#u8,96#u8,205#u8,110#u8,97#u8,108#u8,185#u8,18#u8,37#u8,34#u8,69#u8,172#u8,22#u8,11#u8,120#u8,116#u8,199#u8,39#u8,121#u8,51#u8,199#u8,92#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 1056851884#u32 1665049839#u32 1624045842#u32 1818324685#u32 572854969#u32 186035269#u32 667382904#u32 1556558713#u32

theorem selected : ((JFn_ValueBlock.value ⟨3,by decide⟩).val.drop 32).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 32 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=1056851884#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=1665049839#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1624045842#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=1818324685#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=572854969#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=186035269#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=667382904#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=1556558713#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 1056851884<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 1665049839<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1624045842<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 1818324685<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 572854969<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 186035269<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 667382904<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 1556558713<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨3,by decide⟩) 1#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 1#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value03_1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value03_2
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [162#u8,99#u8,171#u8,46#u8,189#u8,31#u8,247#u8,6#u8,190#u8,45#u8,39#u8,112#u8,138#u8,216#u8,51#u8,51#u8,212#u8,78#u8,180#u8,56#u8,88#u8,200#u8,185#u8,102#u8,31#u8,207#u8,211#u8,23#u8,61#u8,211#u8,138#u8,70#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 782984098#u32 116858813#u32 1881615806#u32 859035786#u32 951340756#u32 1723451480#u32 399757087#u32 1183503165#u32

theorem selected : ((JFn_ValueBlock.value ⟨3,by decide⟩).val.drop 64).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 64 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=782984098#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=116858813#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1881615806#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=859035786#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=951340756#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=1723451480#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=399757087#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=1183503165#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 782984098<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 116858813<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1881615806<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 859035786<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 951340756<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 1723451480<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 399757087<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 1183503165<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨3,by decide⟩) 2#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 2#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value03_2
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value03_3
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [66#u8,233#u8,51#u8,80#u8,38#u8,123#u8,14#u8,15#u8,15#u8,61#u8,51#u8,125#u8,208#u8,194#u8,122#u8,37#u8,196#u8,157#u8,163#u8,14#u8,174#u8,240#u8,244#u8,109#u8,224#u8,92#u8,240#u8,93#u8,250#u8,4#u8,96#u8,82#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 1345579330#u32 252607270#u32 2100509967#u32 628802256#u32 245603780#u32 1844768942#u32 1576033504#u32 1382024442#u32

theorem selected : ((JFn_ValueBlock.value ⟨3,by decide⟩).val.drop 96).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 96 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=1345579330#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=252607270#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=2100509967#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=628802256#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=245603780#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=1844768942#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=1576033504#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=1382024442#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 1345579330<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 252607270<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 2100509967<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 628802256<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 245603780<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 1844768942<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 1576033504<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 1382024442<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨3,by decide⟩) 3#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 3#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value03_3
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Values3
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JGw_Value03_0.value,SAQ_RecordDecode.fromRecord JGw_Value03_1.value,SAQ_RecordDecode.fromRecord JGw_Value03_2.value,SAQ_RecordDecode.fromRecord JGw_Value03_3.value]
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨3,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨3,by decide⟩ _ _ _ _
    JGw_Value03_0.source JGw_Value03_1.source JGw_Value03_2.source JGw_Value03_3.source
#print axioms source
end AspisR1.JGw_Values3
end
