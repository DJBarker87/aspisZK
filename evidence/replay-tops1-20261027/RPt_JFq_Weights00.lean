import RPt_JFq_Scalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight00
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [207#u8,95#u8,150#u8,15#u8,45#u8,12#u8,202#u8,98#u8,17#u8,162#u8,150#u8,101#u8,83#u8,224#u8,64#u8,53#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 712).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 712).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 712#usize)=
    ok (value,JFq_Raw.reader 728#usize) :=
  JFq_Raw.source 712#usize 16#usize 728#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨261513167#u32,1657408557#u32⟩,⟨1704370705#u32,893444179#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 261513167#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 1657408557#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 1704370705#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 893444179#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 261513167 < 2147483647 ∧ 1657408557 < 2147483647 ∧ 1704370705 < 2147483647 ∧ 893444179 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 712#usize)=
    ok (.Ok scalar,JFq_Raw.reader 728#usize) :=
  JFq_Scalar.k 712#usize 728#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight00
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight01
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [140#u8,129#u8,45#u8,28#u8,137#u8,64#u8,132#u8,46#u8,176#u8,43#u8,72#u8,41#u8,151#u8,153#u8,59#u8,57#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 728).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 728).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 728#usize)=
    ok (value,JFq_Raw.reader 744#usize) :=
  JFq_Raw.source 728#usize 16#usize 744#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨472744332#u32,780419209#u32⟩,⟨692595632#u32,960207255#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 472744332#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 780419209#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 692595632#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 960207255#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 472744332 < 2147483647 ∧ 780419209 < 2147483647 ∧ 692595632 < 2147483647 ∧ 960207255 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 728#usize)=
    ok (.Ok scalar,JFq_Raw.reader 744#usize) :=
  JFq_Scalar.k 728#usize 744#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight01
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight02
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [19#u8,52#u8,219#u8,5#u8,129#u8,255#u8,21#u8,115#u8,2#u8,34#u8,138#u8,44#u8,238#u8,198#u8,176#u8,3#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 744).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 744).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 744#usize)=
    ok (value,JFq_Raw.reader 760#usize) :=
  JFq_Raw.source 744#usize 16#usize 760#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨98251795#u32,1930821505#u32⟩,⟨747250178#u32,61916910#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 98251795#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 1930821505#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 747250178#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 61916910#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 98251795 < 2147483647 ∧ 1930821505 < 2147483647 ∧ 747250178 < 2147483647 ∧ 61916910 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 744#usize)=
    ok (.Ok scalar,JFq_Raw.reader 760#usize) :=
  JFq_Scalar.k 744#usize 760#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight02
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Weight03
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [64#u8,86#u8,132#u8,51#u8,241#u8,35#u8,134#u8,71#u8,134#u8,124#u8,177#u8,103#u8,253#u8,10#u8,190#u8,75#u8]
theorem length : bytes.length=16 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 16#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 760).take 16=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 760).take 16=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 16#usize (JFq_Raw.reader 760#usize)=
    ok (value,JFq_Raw.reader 776#usize) :=
  JFq_Raw.source 760#usize 16#usize 776#usize value (by decide) rfl selected

def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 := ⟨⟨864310848#u32,1199973361#u32⟩,⟨1739684998#u32,1270745853#u32⟩⟩
theorem decode : OraclePortCkptAbi2Extracted.decode_k_spec (Array.to_slice value)=ok (some decoded) := by
  have h0 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 0#usize=ok 864310848#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 0#usize (by change 0+4≤16;omega) using 1 <;> rfl
  have h1 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 4#usize=ok 1199973361#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 4#usize (by change 4+4≤16;omega) using 1 <;> rfl
  have h2 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 8#usize=ok 1739684998#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 8#usize (by change 8+4≤16;omega) using 1 <;> rfl
  have h3 : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) 12#usize=ok 1270745853#u32 := by
    convert CheckpointBytes3Word.word_total (Array.to_slice value) 12#usize (by change 12+4≤16;omega) using 1 <;> rfl
  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]
  rw [if_pos (by change 864310848 < 2147483647 ∧ 1199973361 < 2147483647 ∧ 1739684998 < 2147483647 ∧ 1270745853 < 2147483647;decide)]
  rfl

def scalar := CheckpointBytes3Namespaces.fromK decoded
theorem source : CheckpointBytes3Reader.readK (JFq_Raw.reader 760#usize)=
    ok (.Ok scalar,JFq_Raw.reader 776#usize) :=
  JFq_Scalar.k 760#usize 776#usize value decoded raw decode
#print axioms decode
#print axioms source

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_Weight03
end

noncomputable section
namespace AspisR1.JFq_WeightBlock00
open Aeneas Aeneas.Std Result AspisR1Stage2
def values : List aspis_core.field.QM31 := [JFq_Weight00.scalar,JFq_Weight01.scalar,JFq_Weight02.scalar,JFq_Weight03.scalar]
theorem source : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 4 712#usize=ok (.Ok (values,776#usize)) := by
  have step0 := JFq_Weight00.source
  dsimp only [JFq_Raw.reader] at step0
  have step1 := JFq_Weight01.source
  dsimp only [JFq_Raw.reader] at step1
  have step2 := JFq_Weight02.source
  dsimp only [JFq_Raw.reader] at step2
  have step3 := JFq_Weight03.source
  dsimp only [JFq_Raw.reader] at step3
  simp only [Port5Q2_ReaderWeights.reads,step0,step1,step2,step3,
    bind_tc_ok,Aeneas.Std.uncurry]
  rfl
#print axioms source
end AspisR1.JFq_WeightBlock00
end
