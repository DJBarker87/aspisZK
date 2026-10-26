import JFo_QueryRead
import JFo_QueryIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_Opening21_3
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [168#u8,111#u8,35#u8,33#u8,155#u8,205#u8,166#u8,28#u8,212#u8,22#u8,169#u8,112#u8,104#u8,65#u8,229#u8,14#u8,46#u8,213#u8,13#u8,46#u8,93#u8,19#u8,117#u8,12#u8,104#u8,9#u8,193#u8,45#u8,58#u8,225#u8,239#u8,80#u8]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed 555970472#u32 480693659#u32 1890129620#u32 249905512#u32 772658478#u32 208999261#u32 767625576#u32 1357898042#u32

theorem selected : ((JFo_Opening.value ⟨21,by decide⟩).val.drop 96).take 32=arr.val := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 96 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem word0 : wordLE arr 0=555970472#u32 := rfl
#print axioms word0
theorem word1 : wordLE arr 1=480693659#u32 := rfl
#print axioms word1
theorem word2 : wordLE arr 2=1890129620#u32 := rfl
#print axioms word2
theorem word3 : wordLE arr 3=249905512#u32 := rfl
#print axioms word3
theorem word4 : wordLE arr 4=772658478#u32 := rfl
#print axioms word4
theorem word5 : wordLE arr 5=208999261#u32 := rfl
#print axioms word5
theorem word6 : wordLE arr 6=767625576#u32 := rfl
#print axioms word6
theorem word7 : wordLE arr 7=1357898042#u32 := rfl
#print axioms word7

theorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by
  apply (fixed_success_iff arr value).mpr
  constructor
  · intro n
    fin_cases n
    · change (wordLE arr 0).val<2147483647
      rw [word0]
      change 555970472<2147483647
      omega
    · change (wordLE arr 1).val<2147483647
      rw [word1]
      change 480693659<2147483647
      omega
    · change (wordLE arr 2).val<2147483647
      rw [word2]
      change 1890129620<2147483647
      omega
    · change (wordLE arr 3).val<2147483647
      rw [word3]
      change 249905512<2147483647
      omega
    · change (wordLE arr 4).val<2147483647
      rw [word4]
      change 772658478<2147483647
      omega
    · change (wordLE arr 5).val<2147483647
      rw [word5]
      change 208999261<2147483647
      omega
    · change (wordLE arr 6).val<2147483647
      rw [word6]
      change 767625576<2147483647
      omega
    · change (wordLE arr 7).val<2147483647
      rw [word7]
      change 1357898042<2147483647
      omega
  · simp only [word0,word1,word2,word3,word4,word5,word6,word7]
    rfl

theorem source : SAQ_Decoder.read (JFo_Opening.value ⟨21,by decide⟩) 3#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFo_QueryRead.source _ 3#usize (by decide) (JFo_Opening.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JFo_Opening21_3
end
