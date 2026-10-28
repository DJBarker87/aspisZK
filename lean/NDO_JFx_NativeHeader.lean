import RPz8_JFx_NativeBytes
import RPz7_Op3I_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFx_NativeHeader
open Aeneas Aeneas.Std Result
open JFx_NativeBytes

theorem first_sixteen : proof.val.take 16 =
    [82#u8,49#u8,80#u8,51#u8,67#u8,66#u8,49#u8,56#u8,2#u8,
      0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8] := by
  change proofBytes.take 16 = _
  simp only [proofBytes,List.take_append,List.length_append,
    JFx_DataProof00.length,
    JFx_DataProof01.length,
    JFx_DataProof02.length,
    JFx_DataProof03.length,
    JFx_DataProof04.length,
    JFx_DataProof05.length,
    JFx_DataProof06.length,
    JFx_DataProof07.length,
    JFx_DataProof08.length,
    JFx_DataProof09.length,
    JFx_DataProof10.length,
    JFx_DataProof11.length,
    JFx_DataProof12.length,
    JFx_DataProof13.length,
    JFx_DataProof14.length,
    Nat.reduceAdd,Nat.reduceSub,List.take_zero,List.append_nil]
  simp only [JFx_DataProof00.bytes,List.take_append,List.length_append,
    JFx_DataProof00.c00_length,JFx_DataProof00.c01_length,
    JFx_DataProof00.c02_length,JFx_DataProof00.c03_length,
    JFx_DataProof00.c04_length,JFx_DataProof00.c05_length,
    JFx_DataProof00.c06_length,JFx_DataProof00.c07_length,
    JFx_DataProof00.c08_length,JFx_DataProof00.c09_length,
    JFx_DataProof00.c10_length,JFx_DataProof00.c11_length,
    JFx_DataProof00.c12_length,JFx_DataProof00.c13_length,
    JFx_DataProof00.c14_length,JFx_DataProof00.c15_length,
    JFx_DataProof00.c16_length,JFx_DataProof00.c17_length,
    JFx_DataProof00.c18_length,JFx_DataProof00.c19_length,
    JFx_DataProof00.c20_length,JFx_DataProof00.c21_length,
    JFx_DataProof00.c22_length,JFx_DataProof00.c23_length,
    JFx_DataProof00.c24_length,JFx_DataProof00.c25_length,
    JFx_DataProof00.c26_length,JFx_DataProof00.c27_length,
    JFx_DataProof00.c28_length,JFx_DataProof00.c29_length,
    JFx_DataProof00.c30_length,JFx_DataProof00.c31_length,
    JFx_DataProof00.c32_length,JFx_DataProof00.c33_length,
    JFx_DataProof00.c34_length,JFx_DataProof00.c35_length,
    JFx_DataProof00.c36_length,JFx_DataProof00.c37_length,
    JFx_DataProof00.c38_length,JFx_DataProof00.c39_length,
    JFx_DataProof00.c40_length,JFx_DataProof00.c41_length,
    JFx_DataProof00.c42_length,JFx_DataProof00.c43_length,
    JFx_DataProof00.c44_length,JFx_DataProof00.c45_length,
    JFx_DataProof00.c46_length,JFx_DataProof00.c47_length,
    JFx_DataProof00.c48_length,JFx_DataProof00.c49_length,
    JFx_DataProof00.c50_length,JFx_DataProof00.c51_length,
    JFx_DataProof00.c52_length,JFx_DataProof00.c53_length,
    JFx_DataProof00.c54_length,JFx_DataProof00.c55_length,
    JFx_DataProof00.c56_length,JFx_DataProof00.c57_length,
    JFx_DataProof00.c58_length,JFx_DataProof00.c59_length,
    JFx_DataProof00.c60_length,JFx_DataProof00.c61_length,
    JFx_DataProof00.c62_length,JFx_DataProof00.c63_length,
    Nat.reduceAdd,Nat.reduceSub,List.take_zero,List.append_nil]
  rfl

#print axioms first_sixteen
end AspisR1.JFx_NativeHeader
end
