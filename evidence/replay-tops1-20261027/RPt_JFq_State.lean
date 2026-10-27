import RPt_JFq_Scalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_State
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [221#u8,90#u8,114#u8,244#u8,118#u8,28#u8,79#u8,177#u8,218#u8,241#u8,150#u8,70#u8,88#u8,109#u8,78#u8,121#u8,71#u8,84#u8,228#u8,197#u8,229#u8,251#u8,221#u8,242#u8,14#u8,76#u8,246#u8,26#u8,93#u8,145#u8,251#u8,132#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 32#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop 80).take 32=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop 80).take 32=bytes
  simp only [JFx_DataCheckpoint00.bytes,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem raw : CheckpointBytes3Reader.raw 32#usize (JFq_Raw.reader 80#usize)=
    ok (value,JFq_Raw.reader 112#usize) :=
  JFq_Raw.source 80#usize 32#usize 112#usize value (by decide) rfl selected

#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.JFq_State
end
