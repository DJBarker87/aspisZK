import RPt_JFn_ArrayBuilder
import RPt_JFn_ValueBlock
import RPt_JFo_QueryIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value09_0
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [255#u8,62#u8,107#u8,35#u8,174#u8,53#u8,112#u8,105#u8,160#u8,68#u8,106#u8,94#u8,186#u8,117#u8,162#u8,15#u8,57#u8,146#u8,67#u8,89#u8,172#u8,238#u8,209#u8,61#u8,207#u8,197#u8,52#u8,83#u8,174#u8,24#u8,239#u8,61#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 594231039#u32 1768961454#u32 1584022688#u32 262305210#u32 1497600569#u32 1037168300#u32 1395967439#u32 1039079598#u32

theorem selected : ((JFn_ValueBlock.value ⟨9,by decide⟩).val.drop 0).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 0 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=594231039#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=1768961454#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1584022688#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=262305210#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=1497600569#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=1037168300#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=1395967439#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=1039079598#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 594231039<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 1768961454<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1584022688<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 262305210<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 1497600569<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 1037168300<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 1395967439<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 1039079598<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem query : Array.index_usize JFo_Prepared.value.queries 9#usize=ok 159813#u32 :=
  JFo_QueryIndex.source _ _ (by decide) 159813#u32 rfl
#print axioms query

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨9,by decide⟩) 0#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 0#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value09_0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value09_1
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [189#u8,147#u8,170#u8,89#u8,17#u8,193#u8,54#u8,23#u8,186#u8,191#u8,193#u8,99#u8,81#u8,221#u8,198#u8,54#u8,85#u8,213#u8,148#u8,116#u8,168#u8,99#u8,85#u8,47#u8,150#u8,128#u8,150#u8,19#u8,117#u8,120#u8,23#u8,8#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 1504351165#u32 389464337#u32 1673641914#u32 919002449#u32 1955910997#u32 794125224#u32 328630422#u32 135755893#u32

theorem selected : ((JFn_ValueBlock.value ⟨9,by decide⟩).val.drop 32).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 32 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=1504351165#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=389464337#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1673641914#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=919002449#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=1955910997#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=794125224#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=328630422#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=135755893#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 1504351165<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 389464337<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1673641914<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 919002449<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 1955910997<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 794125224<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 328630422<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 135755893<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨9,by decide⟩) 1#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 1#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value09_1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value09_2
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [97#u8,26#u8,46#u8,2#u8,124#u8,41#u8,158#u8,21#u8,58#u8,142#u8,107#u8,94#u8,58#u8,200#u8,91#u8,50#u8,51#u8,203#u8,103#u8,123#u8,57#u8,113#u8,160#u8,99#u8,5#u8,194#u8,74#u8,103#u8,49#u8,200#u8,101#u8,17#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 36575841#u32 362686844#u32 1584107066#u32 844875834#u32 2070399795#u32 1671459129#u32 1732952581#u32 291883057#u32

theorem selected : ((JFn_ValueBlock.value ⟨9,by decide⟩).val.drop 64).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 64 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=36575841#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=362686844#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1584107066#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=844875834#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=2070399795#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=1671459129#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=1732952581#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=291883057#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 36575841<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 362686844<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1584107066<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 844875834<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 2070399795<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 1671459129<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 1732952581<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 291883057<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨9,by decide⟩) 2#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 2#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value09_2
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value09_3
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [7#u8,164#u8,63#u8,2#u8,150#u8,195#u8,174#u8,110#u8,29#u8,16#u8,143#u8,60#u8,181#u8,214#u8,192#u8,101#u8,216#u8,207#u8,241#u8,116#u8,127#u8,196#u8,117#u8,106#u8,194#u8,63#u8,127#u8,31#u8,30#u8,243#u8,128#u8,19#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 37725191#u32 1856947094#u32 1016008733#u32 1707136693#u32 1962004440#u32 1786102911#u32 528433090#u32 327217950#u32

theorem selected : ((JFn_ValueBlock.value ⟨9,by decide⟩).val.drop 96).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 96 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=37725191#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=1856947094#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1016008733#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=1707136693#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=1962004440#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=1786102911#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=528433090#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=327217950#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 37725191<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 1856947094<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1016008733<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 1707136693<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 1962004440<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 1786102911<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 528433090<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 327217950<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨9,by decide⟩) 3#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 3#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value09_3
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Values9
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JGw_Value09_0.value,SAQ_RecordDecode.fromRecord JGw_Value09_1.value,SAQ_RecordDecode.fromRecord JGw_Value09_2.value,SAQ_RecordDecode.fromRecord JGw_Value09_3.value]
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨9,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨9,by decide⟩ _ _ _ _
    JGw_Value09_0.source JGw_Value09_1.source JGw_Value09_2.source JGw_Value09_3.source
#print axioms source
end AspisR1.JGw_Values9
end
