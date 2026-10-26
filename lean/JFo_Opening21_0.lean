import JFo_QueryRead
import JFo_QueryIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_Opening21_0
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [206#u8,232#u8,31#u8,119#u8,153#u8,183#u8,87#u8,7#u8,10#u8,63#u8,89#u8,70#u8,80#u8,8#u8,180#u8,98#u8,90#u8,43#u8,45#u8,119#u8,145#u8,235#u8,85#u8,60#u8,226#u8,174#u8,23#u8,123#u8,248#u8,79#u8,247#u8,1#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 1998579918#u32 123189145#u32 1180253962#u32 1655965776#u32 1999448922#u32 1012263825#u32 2065149666#u32 32985080#u32

theorem selected : ((JFo_Opening.value ⟨21,by decide⟩).val.drop 0).take 32=arr.val := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 0 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=1998579918#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=123189145#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1180253962#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=1655965776#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=1999448922#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=1012263825#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=2065149666#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=32985080#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 1998579918<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 123189145<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1180253962<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 1655965776<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 1999448922<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 1012263825<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 2065149666<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 32985080<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem query : Array.index_usize JFo_Prepared.value.queries 21#usize=ok 14297#u32 :=
  JFo_QueryIndex.source _ _ (by decide) 14297#u32 rfl
#print axioms query

theorem source : SAQ_Decoder.read (JFo_Opening.value ⟨21,by decide⟩) 0#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFo_QueryRead.source _ 0#usize (by decide) (JFo_Opening.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JFo_Opening21_0
end
