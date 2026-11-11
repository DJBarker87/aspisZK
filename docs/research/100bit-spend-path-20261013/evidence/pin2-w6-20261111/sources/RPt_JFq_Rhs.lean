import RPt_JFq_Scalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Rhs
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [252#u8,65#u8,235#u8,103#u8,79#u8,243#u8,118#u8,113#u8,37#u8,68#u8,161#u8,36#u8,60#u8,202#u8,132#u8,108#u8,191#u8,58#u8,127#u8,54#u8,108#u8,77#u8,2#u8,24#u8,82#u8,249#u8,94#u8,97#u8,142#u8,244#u8,73#u8,86#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 32#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 664).take 32=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 664).take 32=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 32#usize (JFq_Raw.reader 664#usize)=
    ok (value,JFq_Raw.reader 696#usize) :=
  JFq_Raw.source 664#usize 32#usize 696#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact := ⟨⟨⟨1743471100#u32,1903620943#u32⟩,⟨614548517#u32,1820641852#u32⟩⟩,⟨⟨914307775#u32,402804076#u32⟩,⟨1633614162#u32,1447687310#u32⟩⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_e_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 1743471100#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤32;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 1903620943#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤32;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 614548517#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤32;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 1820641852#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤32;omega) using 1 <;> rfl
  have h4 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 16#usize=ok 914307775#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 16#usize (by change 16+4≤32;omega) using 1 <;> rfl
  have h5 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 20#usize=ok 402804076#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 20#usize (by change 20+4≤32;omega) using 1 <;> rfl
  have h6 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 24#usize=ok 1633614162#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 24#usize (by change 24+4≤32;omega) using 1 <;> rfl
  have h7 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 28#usize=ok 1447687310#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 28#usize (by change 28+4≤32;omega) using 1 <;> rfl
  let words : Fin 8 → U32 := ![1743471100#u32,1903620943#u32,614548517#u32,1820641852#u32,914307775#u32,402804076#u32,1633614162#u32,1447687310#u32]
  rw [CheckpointBytes3EShape.e_shape _ (by exact value.property) words h0 h1 h2 h3 h4 h5 h6 h7]
  rw [if_pos (by change (1743471100 < 2147483647 ∧ 1903620943 < 2147483647 ∧ 614548517 < 2147483647 ∧ 1820641852 < 2147483647) ∧ (914307775 < 2147483647 ∧ 402804076 < 2147483647 ∧ 1633614162 < 2147483647 ∧ 1447687310 < 2147483647);decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromE decoded
theorem source : CheckpointBytes3Reader.readE (JFq_Raw.reader 664#usize)=
    ok (.Ok scalar,JFq_Raw.reader 696#usize) :=
  JFq_Scalar.e 664#usize 696#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Rhs
end
