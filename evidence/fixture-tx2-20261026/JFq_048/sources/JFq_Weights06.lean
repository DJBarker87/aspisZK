import JFq_Scalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight24
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [182#u8,56#u8,134#u8,115#u8,115#u8,171#u8,96#u8,52#u8,108#u8,191#u8,171#u8,27#u8,237#u8,215#u8,20#u8,22#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 1096).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 1096).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 1096#usize)=
    ok (value,JFq_Raw.reader 1112#usize) :=
  JFq_Raw.source 1096#usize 16#usize 1112#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨1938176182#u32,878750579#u32⟩,⟨464240492#u32,370464749#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 1938176182#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 878750579#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 464240492#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 370464749#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 1938176182 < 2147483647 ∧ 878750579 < 2147483647 ∧ 464240492 < 2147483647 ∧ 370464749 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 1096#usize)=
    ok (.Ok scalar,JFq_Raw.reader 1112#usize) :=
  JFq_Scalar.k 1096#usize 1112#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight24
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight25
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [227#u8,106#u8,90#u8,92#u8,99#u8,25#u8,46#u8,23#u8,255#u8,239#u8,233#u8,123#u8,93#u8,30#u8,165#u8,36#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 1112).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 1112).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 1112#usize)=
    ok (value,JFq_Raw.reader 1128#usize) :=
  JFq_Raw.source 1112#usize 16#usize 1128#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨1549429475#u32,388897123#u32⟩,⟨2078928895#u32,614800989#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 1549429475#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 388897123#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 2078928895#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 614800989#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 1549429475 < 2147483647 ∧ 388897123 < 2147483647 ∧ 2078928895 < 2147483647 ∧ 614800989 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 1112#usize)=
    ok (.Ok scalar,JFq_Raw.reader 1128#usize) :=
  JFq_Scalar.k 1112#usize 1128#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight25
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight26
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [195#u8,131#u8,173#u8,49#u8,255#u8,237#u8,228#u8,121#u8,159#u8,185#u8,193#u8,51#u8,168#u8,88#u8,123#u8,116#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 1128).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 1128).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 1128#usize)=
    ok (value,JFq_Raw.reader 1144#usize) :=
  JFq_Raw.source 1128#usize 16#usize 1144#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨833455043#u32,2045046271#u32⟩,⟨868333983#u32,1954240680#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 833455043#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 2045046271#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 868333983#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 1954240680#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 833455043 < 2147483647 ∧ 2045046271 < 2147483647 ∧ 868333983 < 2147483647 ∧ 1954240680 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 1128#usize)=
    ok (.Ok scalar,JFq_Raw.reader 1144#usize) :=
  JFq_Scalar.k 1128#usize 1144#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight26
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight27
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [131#u8,201#u8,25#u8,70#u8,31#u8,28#u8,134#u8,19#u8,201#u8,168#u8,153#u8,126#u8,245#u8,202#u8,22#u8,23#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 1144).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 1144).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 1144#usize)=
    ok (value,JFq_Raw.reader 1160#usize) :=
  JFq_Raw.source 1144#usize 16#usize 1160#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨1176095107#u32,327556127#u32⟩,⟨2123999433#u32,387369717#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 1176095107#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 327556127#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 2123999433#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 387369717#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 1176095107 < 2147483647 ∧ 327556127 < 2147483647 ∧ 2123999433 < 2147483647 ∧ 387369717 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 1144#usize)=
    ok (.Ok scalar,JFq_Raw.reader 1160#usize) :=
  JFq_Scalar.k 1144#usize 1160#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight27
end

noncomputable section
namespace AspisR1.JFq_WeightBlock06
open Aeneas Aeneas.Std Result AspisR1Stage2
def values : List aspis_core.field.QM31 := [JFq_Weight24.scalar,JFq_Weight25.scalar,JFq_Weight26.scalar,JFq_Weight27.scalar]
theorem source : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 4 1096#usize=ok (.Ok (values,1160#usize)) := by
  have step24 := JFq_Weight24.source
  dsimp only [JFq_Raw.reader] at step24
  have step25 := JFq_Weight25.source
  dsimp only [JFq_Raw.reader] at step25
  have step26 := JFq_Weight26.source
  dsimp only [JFq_Raw.reader] at step26
  have step27 := JFq_Weight27.source
  dsimp only [JFq_Raw.reader] at step27
  simp only [Port5Q2_ReaderWeights.reads,step24,step25,step26,step27,
    bind_tc_ok,Aeneas.Std.uncurry]
  rfl
#print axioms source
end AspisR1.JFq_WeightBlock06
end
