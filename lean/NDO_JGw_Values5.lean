import RPt_JFn_ArrayBuilder
import RPt_JFn_ValueBlock
import RPt_JFo_QueryIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value05_0
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [40#u8,80#u8,209#u8,122#u8,239#u8,14#u8,137#u8,84#u8,244#u8,162#u8,104#u8,7#u8,81#u8,142#u8,250#u8,97#u8,64#u8,135#u8,48#u8,70#u8,2#u8,191#u8,207#u8,46#u8,227#u8,132#u8,227#u8,26#u8,230#u8,237#u8,126#u8,114#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 2060537896#u32 1418268399#u32 124297972#u32 1643810385#u32 1177585472#u32 785366786#u32 451118307#u32 1920921062#u32

theorem selected : ((JFn_ValueBlock.value ⟨5,by decide⟩).val.drop 0).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 0 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=2060537896#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=1418268399#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=124297972#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=1643810385#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=1177585472#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=785366786#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=451118307#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=1920921062#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 2060537896<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 1418268399<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 124297972<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 1643810385<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 1177585472<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 785366786<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 451118307<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 1920921062<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem query : Array.index_usize JFo_Prepared.value.queries 5#usize=ok 192317#u32 :=
  JFo_QueryIndex.source _ _ (by decide) 192317#u32 rfl
#print axioms query

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨5,by decide⟩) 0#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 0#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value05_0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value05_1
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [203#u8,242#u8,129#u8,10#u8,65#u8,14#u8,211#u8,52#u8,11#u8,20#u8,230#u8,127#u8,15#u8,100#u8,80#u8,3#u8,231#u8,112#u8,88#u8,57#u8,230#u8,224#u8,171#u8,92#u8,12#u8,183#u8,110#u8,83#u8,8#u8,142#u8,172#u8,6#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 176288459#u32 886246977#u32 2145784843#u32 55600143#u32 962097383#u32 1554768102#u32 1399764748#u32 111971848#u32

theorem selected : ((JFn_ValueBlock.value ⟨5,by decide⟩).val.drop 32).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 32 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=176288459#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=886246977#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=2145784843#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=55600143#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=962097383#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=1554768102#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=1399764748#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=111971848#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 176288459<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 886246977<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 2145784843<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 55600143<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 962097383<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 1554768102<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 1399764748<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 111971848<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨5,by decide⟩) 1#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 1#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value05_1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value05_2
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [246#u8,5#u8,123#u8,10#u8,24#u8,178#u8,117#u8,48#u8,217#u8,38#u8,158#u8,35#u8,139#u8,28#u8,185#u8,55#u8,220#u8,253#u8,203#u8,52#u8,175#u8,53#u8,167#u8,63#u8,13#u8,125#u8,204#u8,100#u8,176#u8,82#u8,111#u8,108#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 175834614#u32 813019672#u32 597567193#u32 934878347#u32 885784028#u32 1067922863#u32 1691122957#u32 1819234992#u32

theorem selected : ((JFn_ValueBlock.value ⟨5,by decide⟩).val.drop 64).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 64 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=175834614#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=813019672#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=597567193#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=934878347#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=885784028#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=1067922863#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=1691122957#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=1819234992#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 175834614<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 813019672<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 597567193<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 934878347<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 885784028<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 1067922863<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 1691122957<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 1819234992<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨5,by decide⟩) 2#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 2#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value05_2
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Value05_3
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [194#u8,211#u8,207#u8,53#u8,216#u8,59#u8,219#u8,91#u8,220#u8,230#u8,211#u8,95#u8,121#u8,180#u8,52#u8,87#u8,128#u8,117#u8,107#u8,98#u8,150#u8,233#u8,207#u8,110#u8,142#u8,181#u8,221#u8,27#u8,30#u8,47#u8,116#u8,24#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 902812610#u32 1541094360#u32 1607722716#u32 1463071865#u32 1651209600#u32 1859119510#u32 467514766#u32 410267422#u32

theorem selected : ((JFn_ValueBlock.value ⟨5,by decide⟩).val.drop 96).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 96 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=902812610#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=1541094360#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1607722716#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=1463071865#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=1651209600#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=1859119510#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=467514766#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=410267422#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 902812610<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 1541094360<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1607722716<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 1463071865<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 1651209600<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 1859119510<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 467514766<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 410267422<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨5,by decide⟩) 3#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ 3#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Value05_3
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Values5
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JGw_Value05_0.value,SAQ_RecordDecode.fromRecord JGw_Value05_1.value,SAQ_RecordDecode.fromRecord JGw_Value05_2.value,SAQ_RecordDecode.fromRecord JGw_Value05_3.value]
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨5,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨5,by decide⟩ _ _ _ _
    JGw_Value05_0.source JGw_Value05_1.source JGw_Value05_2.source JGw_Value05_3.source
#print axioms source
end AspisR1.JGw_Values5
end
