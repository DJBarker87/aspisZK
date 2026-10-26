import JFq_Scalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Claim
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [192#u8,108#u8,144#u8,98#u8,202#u8,69#u8,182#u8,66#u8,67#u8,126#u8,171#u8,89#u8,244#u8,136#u8,135#u8,72#u8,218#u8,224#u8,64#u8,119#u8,97#u8,98#u8,74#u8,97#u8,57#u8,41#u8,226#u8,92#u8,194#u8,150#u8,124#u8,76#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 32#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 632).take 32=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 632).take 32=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 32#usize (JFq_Raw.reader 632#usize)=
    ok (value,JFq_Raw.reader 664#usize) :=
  JFq_Raw.source 632#usize 32#usize 664#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact := ⟨⟨⟨1653632192#u32,1119241674#u32⟩,⟨1504411203#u32,1216841972#u32⟩⟩,⟨⟨2000740570#u32,1632264801#u32⟩,⟨1558325561#u32,1283233474#u32⟩⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_e_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 1653632192#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤32;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 1119241674#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤32;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 1504411203#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤32;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 1216841972#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤32;omega) using 1 <;> rfl
  have h4 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 16#usize=ok 2000740570#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 16#usize (by change 16+4≤32;omega) using 1 <;> rfl
  have h5 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 20#usize=ok 1632264801#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 20#usize (by change 20+4≤32;omega) using 1 <;> rfl
  have h6 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 24#usize=ok 1558325561#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 24#usize (by change 24+4≤32;omega) using 1 <;> rfl
  have h7 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 28#usize=ok 1283233474#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 28#usize (by change 28+4≤32;omega) using 1 <;> rfl
  let words : Fin 8 → U32 := ![1653632192#u32,1119241674#u32,1504411203#u32,1216841972#u32,2000740570#u32,1632264801#u32,1558325561#u32,1283233474#u32]
  rw [CheckpointBytes3EShape.e_shape _ (by exact value.property) words h0 h1 h2 h3 h4 h5 h6 h7]
  rw [if_pos (by change (1653632192 < 2147483647 ∧ 1119241674 < 2147483647 ∧ 1504411203 < 2147483647 ∧ 1216841972 < 2147483647) ∧ (2000740570 < 2147483647 ∧ 1632264801 < 2147483647 ∧ 1558325561 < 2147483647 ∧ 1283233474 < 2147483647);decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromE decoded
theorem source : CheckpointBytes3Reader.readE (JFq_Raw.reader 632#usize)=
    ok (.Ok scalar,JFq_Raw.reader 664#usize) :=
  JFq_Scalar.e 632#usize 664#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Claim
end
