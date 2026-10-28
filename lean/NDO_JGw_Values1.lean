import RPt_JFn_ArrayBuilder
import RPt_JFn_ValueBlock
import RPt_JFo_QueryIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value01_0
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [47#u8,167#u8,209#u8,86#u8,128#u8,184#u8,43#u8,50#u8,220#u8,197#u8,93#u8,58#u8,100#u8,126#u8,34#u8,110#u8,199#u8,192#u8,68#u8,72#u8,176#u8,1#u8,70#u8,42#u8,252#u8,3#u8,169#u8,16#u8,12#u8,172#u8,174#u8,103#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 1456580399#u32 841726080#u32 979224028#u32 1847754340#u32 1212465351#u32 709231024#u32 279512060#u32 1739500556#u32

theorem selected : ((JFn_ValueBlock.value ⟨1,by decide⟩).val.drop 0).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 0 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=1456580399#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=841726080#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=979224028#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=1847754340#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=1212465351#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=709231024#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=279512060#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=1739500556#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 1456580399<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 841726080<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 979224028<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 1847754340<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 1212465351<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 709231024<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 279512060<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 1739500556<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem query : Array.index_usize JFo_Prepared.value.queries 1#usize=ok 147529#u32 :=
  JFo_QueryIndex.source _ _ (by decide) 147529#u32 rfl
#print axioms query

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨1,by decide⟩) 0#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 0#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value01_0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value01_1
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [36#u8,57#u8,60#u8,0#u8,117#u8,75#u8,130#u8,114#u8,7#u8,186#u8,3#u8,114#u8,149#u8,49#u8,214#u8,4#u8,151#u8,93#u8,74#u8,56#u8,156#u8,119#u8,93#u8,87#u8,131#u8,67#u8,57#u8,41#u8,182#u8,105#u8,221#u8,111#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 3946788#u32 1921141621#u32 1912846855#u32 81146261#u32 944397719#u32 1465743260#u32 691618691#u32 1876781494#u32

theorem selected : ((JFn_ValueBlock.value ⟨1,by decide⟩).val.drop 32).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 32 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=3946788#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=1921141621#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1912846855#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=81146261#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=944397719#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=1465743260#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=691618691#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=1876781494#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 3946788<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 1921141621<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1912846855<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 81146261<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 944397719<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 1465743260<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 691618691<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 1876781494<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨1,by decide⟩) 1#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 1#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value01_1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value01_2
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [93#u8,22#u8,81#u8,67#u8,235#u8,199#u8,207#u8,18#u8,205#u8,30#u8,198#u8,99#u8,37#u8,83#u8,154#u8,86#u8,175#u8,67#u8,56#u8,114#u8,84#u8,225#u8,19#u8,64#u8,14#u8,177#u8,15#u8,41#u8,1#u8,35#u8,201#u8,72#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 1129387613#u32 315607019#u32 1673928397#u32 1452954405#u32 1916289967#u32 1075044692#u32 688894222#u32 1221141249#u32

theorem selected : ((JFn_ValueBlock.value ⟨1,by decide⟩).val.drop 64).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 64 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=1129387613#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=315607019#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1673928397#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=1452954405#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=1916289967#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=1075044692#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=688894222#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=1221141249#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 1129387613<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 315607019<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1673928397<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 1452954405<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 1916289967<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 1075044692<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 688894222<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 1221141249<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨1,by decide⟩) 2#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 2#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value01_2
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value01_3
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [70#u8,136#u8,126#u8,0#u8,241#u8,174#u8,178#u8,93#u8,14#u8,242#u8,159#u8,2#u8,148#u8,74#u8,122#u8,17#u8,145#u8,96#u8,69#u8,15#u8,108#u8,240#u8,107#u8,120#u8,182#u8,238#u8,146#u8,22#u8,20#u8,148#u8,254#u8,17#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 8292422#u32 1571991281#u32 44036622#u32 293227156#u32 256204945#u32 2020339820#u32 378728118#u32 301896724#u32

theorem selected : ((JFn_ValueBlock.value ⟨1,by decide⟩).val.drop 96).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 96 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=8292422#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=1571991281#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=44036622#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=293227156#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=256204945#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=2020339820#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=378728118#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=301896724#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 8292422<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 1571991281<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 44036622<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 293227156<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 256204945<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 2020339820<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 378728118<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 301896724<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨1,by decide⟩) 3#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 3#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value01_3
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Values1
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JGw_Value01_0.value,SAQ_RecordDecode.fromRecord JGw_Value01_1.value,SAQ_RecordDecode.fromRecord JGw_Value01_2.value,SAQ_RecordDecode.fromRecord JGw_Value01_3.value]
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨1,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨1,by decide⟩ _ _ _ _
    JGw_Value01_0.source JGw_Value01_1.source JGw_Value01_2.source JGw_Value01_3.source
#print axioms source
end AspisR1.JGw_Values1
end
