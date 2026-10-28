import NDO_JFz_RowGeometry
import RPz8_JFx_NativeBytes
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JFz_Row12
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical JFz_RowGeometry
theorem header : (JFx_NativeBytes.proof.val.drop 140).take 5 = [0#u8,0#u8,0#u8,0#u8,0#u8] := by
  change (JFx_NativeBytes.proofBytes.drop _).take _ = _
  simp only [JFx_NativeBytes.proofBytes,List.drop_append,List.take_append,List.length_append,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof00.bytes,JFx_DataProof00.c00_length,JFx_DataProof00.c01_length,JFx_DataProof00.c02_length,JFx_DataProof00.c03_length,JFx_DataProof00.c04_length,JFx_DataProof00.c05_length,JFx_DataProof00.c06_length,JFx_DataProof00.c07_length,JFx_DataProof00.c08_length,JFx_DataProof00.c09_length,JFx_DataProof00.c10_length,JFx_DataProof00.c11_length,JFx_DataProof00.c12_length,JFx_DataProof00.c13_length,JFx_DataProof00.c14_length,JFx_DataProof00.c15_length,JFx_DataProof00.c16_length,JFx_DataProof00.c17_length,JFx_DataProof00.c18_length,JFx_DataProof00.c19_length,JFx_DataProof00.c20_length,JFx_DataProof00.c21_length,JFx_DataProof00.c22_length,JFx_DataProof00.c23_length,JFx_DataProof00.c24_length,JFx_DataProof00.c25_length,JFx_DataProof00.c26_length,JFx_DataProof00.c27_length,JFx_DataProof00.c28_length,JFx_DataProof00.c29_length,JFx_DataProof00.c30_length,JFx_DataProof00.c31_length,JFx_DataProof00.c32_length,JFx_DataProof00.c33_length,JFx_DataProof00.c34_length,JFx_DataProof00.c35_length,JFx_DataProof00.c36_length,JFx_DataProof00.c37_length,JFx_DataProof00.c38_length,JFx_DataProof00.c39_length,JFx_DataProof00.c40_length,JFx_DataProof00.c41_length,JFx_DataProof00.c42_length,JFx_DataProof00.c43_length,JFx_DataProof00.c44_length,JFx_DataProof00.c45_length,JFx_DataProof00.c46_length,JFx_DataProof00.c47_length,JFx_DataProof00.c48_length,JFx_DataProof00.c49_length,JFx_DataProof00.c50_length,JFx_DataProof00.c51_length,JFx_DataProof00.c52_length,JFx_DataProof00.c53_length,JFx_DataProof00.c54_length,JFx_DataProof00.c55_length,JFx_DataProof00.c56_length,JFx_DataProof00.c57_length,JFx_DataProof00.c58_length,JFx_DataProof00.c59_length,JFx_DataProof00.c60_length,JFx_DataProof00.c61_length,JFx_DataProof00.c62_length,JFx_DataProof00.c63_length,JFx_DataProof00.c64_length,JFx_DataProof00.c65_length,JFx_DataProof00.c66_length,JFx_DataProof00.c67_length,JFx_DataProof00.c68_length,JFx_DataProof00.c69_length,JFx_DataProof00.c70_length,JFx_DataProof00.c71_length,JFx_DataProof00.c72_length,JFx_DataProof00.c73_length,JFx_DataProof00.c74_length,JFx_DataProof00.c75_length,JFx_DataProof00.c76_length,JFx_DataProof00.c77_length,JFx_DataProof00.c78_length,JFx_DataProof00.c79_length,JFx_DataProof00.c80_length,JFx_DataProof00.c81_length,JFx_DataProof00.c82_length,JFx_DataProof00.c83_length,JFx_DataProof00.c84_length,JFx_DataProof00.c85_length,JFx_DataProof00.c86_length,JFx_DataProof00.c87_length,JFx_DataProof00.c88_length,JFx_DataProof00.c89_length,JFx_DataProof00.c90_length,JFx_DataProof00.c91_length,JFx_DataProof00.c92_length,JFx_DataProof00.c93_length,JFx_DataProof00.c94_length,JFx_DataProof00.c95_length,JFx_DataProof00.c96_length,JFx_DataProof00.c97_length,JFx_DataProof00.c98_length,JFx_DataProof00.c99_length,JFx_DataProof00.c100_length,JFx_DataProof00.c101_length,JFx_DataProof00.c102_length,JFx_DataProof00.c103_length,JFx_DataProof00.c104_length,JFx_DataProof00.c105_length,JFx_DataProof00.c106_length,JFx_DataProof00.c107_length,JFx_DataProof00.c108_length,JFx_DataProof00.c109_length,JFx_DataProof00.c110_length,JFx_DataProof00.c111_length,JFx_DataProof00.c112_length,JFx_DataProof00.c113_length,JFx_DataProof00.c114_length,JFx_DataProof00.c115_length,JFx_DataProof00.c116_length,JFx_DataProof00.c117_length,JFx_DataProof00.c118_length,JFx_DataProof00.c119_length,JFx_DataProof00.c120_length,JFx_DataProof00.c121_length,JFx_DataProof00.c122_length,JFx_DataProof00.c123_length,JFx_DataProof00.c124_length,JFx_DataProof00.c125_length,JFx_DataProof00.c126_length,JFx_DataProof00.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms header
theorem shape : rowShape 12 = (0,0) := by norm_num [rowShape]
theorem step (rs : List Bytes)
    (tail : semanticRows 14 13 (slice wire 145 6886) = some rs) :
    semanticRows 15 12 (slice wire 140 6891) =
      some (PSem_Rows.expandedRow 12 (slice wire 140 6891) :: rs) := by
  refine JFz_RowGeometry.forward 14 12 _ rs ?_ ?_ ?_ ?_
  · norm_num only [shape,Prod.snd,if_neg (by decide : ¬ 14 ≤ 12)]
    rw [slice,List.length_take,List.length_drop,wire_length]
    decide
  · rw [shape]
    rw [slice_take _ 140 5 6891 (by decide)]
    simp only [slice,wire,bytesOf, ← List.map_drop, ← List.map_take,header]
    rfl
  · intro compact
    omega
  · norm_num only [shape,Prod.snd,if_neg (by decide : ¬ 14 ≤ 12)]
    rw [slice_drop]
    exact tail
#print axioms shape
#print axioms step
end AspisR1.JFz_Row12
end
