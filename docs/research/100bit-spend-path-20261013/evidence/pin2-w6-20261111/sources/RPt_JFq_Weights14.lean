import RPt_JFq_Scalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight56
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [68#u8,217#u8,110#u8,120#u8,151#u8,86#u8,67#u8,121#u8,211#u8,30#u8,137#u8,87#u8,93#u8,35#u8,176#u8,5#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 1608).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 1608).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 1608#usize)=
    ok (value,JFq_Raw.reader 1624#usize) :=
  JFq_Raw.source 1608#usize 16#usize 1624#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨2020530500#u32,2034456215#u32⟩,⟨1468604115#u32,95429469#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 2020530500#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 2034456215#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 1468604115#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 95429469#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 2020530500 < 2147483647 ∧ 2034456215 < 2147483647 ∧ 1468604115 < 2147483647 ∧ 95429469 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 1608#usize)=
    ok (.Ok scalar,JFq_Raw.reader 1624#usize) :=
  JFq_Scalar.k 1608#usize 1624#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight56
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight57
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [65#u8,196#u8,244#u8,77#u8,227#u8,138#u8,82#u8,43#u8,98#u8,135#u8,222#u8,111#u8,184#u8,189#u8,246#u8,31#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 1624).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 1624).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 1624#usize)=
    ok (value,JFq_Raw.reader 1640#usize) :=
  JFq_Raw.source 1624#usize 16#usize 1640#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨1307886657#u32,726829795#u32⟩,⟨1876854626#u32,536264120#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 1307886657#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 726829795#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 1876854626#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 536264120#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 1307886657 < 2147483647 ∧ 726829795 < 2147483647 ∧ 1876854626 < 2147483647 ∧ 536264120 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 1624#usize)=
    ok (.Ok scalar,JFq_Raw.reader 1640#usize) :=
  JFq_Scalar.k 1624#usize 1640#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight57
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight58
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [126#u8,11#u8,88#u8,32#u8,242#u8,117#u8,127#u8,100#u8,65#u8,201#u8,45#u8,66#u8,77#u8,126#u8,144#u8,32#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 1640).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 1640).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 1640#usize)=
    ok (value,JFq_Raw.reader 1656#usize) :=
  JFq_Raw.source 1640#usize 16#usize 1656#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨542641022#u32,1686074866#u32⟩,⟨1110296897#u32,546340429#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 542641022#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 1686074866#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 1110296897#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 546340429#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 542641022 < 2147483647 ∧ 1686074866 < 2147483647 ∧ 1110296897 < 2147483647 ∧ 546340429 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 1640#usize)=
    ok (.Ok scalar,JFq_Raw.reader 1656#usize) :=
  JFq_Scalar.k 1640#usize 1656#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight58
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight59
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [48#u8,221#u8,86#u8,125#u8,21#u8,48#u8,205#u8,90#u8,85#u8,121#u8,195#u8,13#u8,133#u8,246#u8,79#u8,1#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 1656).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 1656).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 1656#usize)=
    ok (value,JFq_Raw.reader 1672#usize) :=
  JFq_Raw.source 1656#usize 16#usize 1672#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨2102844720#u32,1523396629#u32⟩,⟨230914389#u32,22017669#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 2102844720#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 1523396629#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 230914389#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 22017669#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 2102844720 < 2147483647 ∧ 1523396629 < 2147483647 ∧ 230914389 < 2147483647 ∧ 22017669 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 1656#usize)=
    ok (.Ok scalar,JFq_Raw.reader 1672#usize) :=
  JFq_Scalar.k 1656#usize 1672#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight59
end

noncomputable section
namespace AspisR1.JFq_WeightBlock14
open Aeneas Aeneas.Std Result AspisR1Stage2
def values : List aspis_core.field.QM31 := [JFq_Weight56.scalar,JFq_Weight57.scalar,JFq_Weight58.scalar,JFq_Weight59.scalar]
theorem source : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 4 1608#usize=ok (.Ok (values,1672#usize)) := by
  have step56 := JFq_Weight56.source
  dsimp only [JFq_Raw.reader] at step56
  have step57 := JFq_Weight57.source
  dsimp only [JFq_Raw.reader] at step57
  have step58 := JFq_Weight58.source
  dsimp only [JFq_Raw.reader] at step58
  have step59 := JFq_Weight59.source
  dsimp only [JFq_Raw.reader] at step59
  simp only [Port5Q2_ReaderWeights.reads,step56,step57,step58,step59,
    bind_tc_ok,Aeneas.Std.uncurry]
  rfl
#print axioms source
end AspisR1.JFq_WeightBlock14
end
