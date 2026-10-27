import RPt_JFq_Scalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight36
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [138#u8,204#u8,53#u8,40#u8,213#u8,187#u8,205#u8,48#u8,36#u8,91#u8,78#u8,33#u8,123#u8,72#u8,3#u8,13#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 1288).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 1288).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 1288#usize)=
    ok (value,JFq_Raw.reader 1304#usize) :=
  JFq_Raw.source 1288#usize 16#usize 1304#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨674614410#u32,818789333#u32⟩,⟨558783268#u32,218318971#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 674614410#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 818789333#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 558783268#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 218318971#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 674614410 < 2147483647 ∧ 818789333 < 2147483647 ∧ 558783268 < 2147483647 ∧ 218318971 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 1288#usize)=
    ok (.Ok scalar,JFq_Raw.reader 1304#usize) :=
  JFq_Scalar.k 1288#usize 1304#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight36
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight37
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [149#u8,63#u8,41#u8,102#u8,135#u8,32#u8,196#u8,85#u8,73#u8,101#u8,160#u8,77#u8,47#u8,177#u8,214#u8,8#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 1304).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 1304).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 1304#usize)=
    ok (value,JFq_Raw.reader 1320#usize) :=
  JFq_Raw.source 1304#usize 16#usize 1320#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨1713979285#u32,1438916743#u32⟩,⟨1302357321#u32,148287791#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 1713979285#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 1438916743#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 1302357321#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 148287791#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 1713979285 < 2147483647 ∧ 1438916743 < 2147483647 ∧ 1302357321 < 2147483647 ∧ 148287791 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 1304#usize)=
    ok (.Ok scalar,JFq_Raw.reader 1320#usize) :=
  JFq_Scalar.k 1304#usize 1320#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight37
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight38
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [99#u8,198#u8,18#u8,11#u8,216#u8,73#u8,188#u8,78#u8,175#u8,36#u8,193#u8,89#u8,172#u8,50#u8,65#u8,106#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 1320).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 1320).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 1320#usize)=
    ok (value,JFq_Raw.reader 1336#usize) :=
  JFq_Raw.source 1320#usize 16#usize 1336#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨185779811#u32,1320962520#u32⟩,⟨1505830063#u32,1782657708#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 185779811#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 1320962520#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 1505830063#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 1782657708#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 185779811 < 2147483647 ∧ 1320962520 < 2147483647 ∧ 1505830063 < 2147483647 ∧ 1782657708 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 1320#usize)=
    ok (.Ok scalar,JFq_Raw.reader 1336#usize) :=
  JFq_Scalar.k 1320#usize 1336#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight38
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight39
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [74#u8,70#u8,212#u8,89#u8,27#u8,148#u8,89#u8,126#u8,161#u8,114#u8,212#u8,32#u8,99#u8,80#u8,90#u8,124#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 1336).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 1336).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 1336#usize)=
    ok (value,JFq_Raw.reader 1352#usize) :=
  JFq_Raw.source 1336#usize 16#usize 1352#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨1507083850#u32,2119799835#u32⟩,⟨550793889#u32,2086293603#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 1507083850#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 2119799835#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 550793889#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 2086293603#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 1507083850 < 2147483647 ∧ 2119799835 < 2147483647 ∧ 550793889 < 2147483647 ∧ 2086293603 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 1336#usize)=
    ok (.Ok scalar,JFq_Raw.reader 1352#usize) :=
  JFq_Scalar.k 1336#usize 1352#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight39
end

noncomputable section
namespace AspisR1.JFq_WeightBlock09
open Aeneas Aeneas.Std Result AspisR1Stage2
def values : List aspis_core.field.QM31 := [JFq_Weight36.scalar,JFq_Weight37.scalar,JFq_Weight38.scalar,JFq_Weight39.scalar]
theorem source : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 4 1288#usize=ok (.Ok (values,1352#usize)) := by
  have step36 := JFq_Weight36.source
  dsimp only [JFq_Raw.reader] at step36
  have step37 := JFq_Weight37.source
  dsimp only [JFq_Raw.reader] at step37
  have step38 := JFq_Weight38.source
  dsimp only [JFq_Raw.reader] at step38
  have step39 := JFq_Weight39.source
  dsimp only [JFq_Raw.reader] at step39
  simp only [Port5Q2_ReaderWeights.reads,step36,step37,step38,step39,
    bind_tc_ok,Aeneas.Std.uncurry]
  rfl
#print axioms source
end AspisR1.JFq_WeightBlock09
end
