import JFq_Scalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Gamma
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [235#u8,4#u8,0#u8,51#u8,247#u8,16#u8,103#u8,88#u8,217#u8,32#u8,44#u8,113#u8,70#u8,87#u8,65#u8,110#u8,253#u8,249#u8,77#u8,66#u8,17#u8,56#u8,25#u8,107#u8,107#u8,253#u8,155#u8,109#u8,76#u8,18#u8,245#u8,24#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 32#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 176).take 32=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 176).take 32=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 32#usize (JFq_Raw.reader 176#usize)=
    ok (value,JFq_Raw.reader 208#usize) :=
  JFq_Raw.source 176#usize 32#usize 208#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact := ⟨⟨⟨855639275#u32,1483149559#u32⟩,⟨1898717401#u32,1849775942#u32⟩⟩,⟨⟨1112406525#u32,1796814865#u32⟩,⟨1838939499#u32,418714188#u32⟩⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_e_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 855639275#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤32;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 1483149559#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤32;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 1898717401#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤32;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 1849775942#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤32;omega) using 1 <;> rfl
  have h4 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 16#usize=ok 1112406525#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 16#usize (by change 16+4≤32;omega) using 1 <;> rfl
  have h5 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 20#usize=ok 1796814865#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 20#usize (by change 20+4≤32;omega) using 1 <;> rfl
  have h6 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 24#usize=ok 1838939499#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 24#usize (by change 24+4≤32;omega) using 1 <;> rfl
  have h7 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 28#usize=ok 418714188#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 28#usize (by change 28+4≤32;omega) using 1 <;> rfl
  let words : Fin 8 → U32 := ![855639275#u32,1483149559#u32,1898717401#u32,1849775942#u32,1112406525#u32,1796814865#u32,1838939499#u32,418714188#u32]
  rw [CheckpointBytes3EShape.e_shape _ (by exact value.property) words h0 h1 h2 h3 h4 h5 h6 h7]
  rw [if_pos (by change (855639275 < 2147483647 ∧ 1483149559 < 2147483647 ∧ 1898717401 < 2147483647 ∧ 1849775942 < 2147483647) ∧ (1112406525 < 2147483647 ∧ 1796814865 < 2147483647 ∧ 1838939499 < 2147483647 ∧ 418714188 < 2147483647);decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromE decoded
theorem source : CheckpointBytes3Reader.readE (JFq_Raw.reader 176#usize)=
    ok (.Ok scalar,JFq_Raw.reader 208#usize) :=
  JFq_Scalar.e 176#usize 208#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Gamma
end
