import NDO_JFz_Scan57
import NDO_JFz_RowGeometry
import RPz8_JFx_NativeBytes
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JFz_Row24
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical JFz_RowGeometry
theorem header : (JFx_NativeBytes.proof.val.drop 4248).take 5 = [2#u8,128#u8,3#u8,0#u8,0#u8] := by
  change (JFx_NativeBytes.proofBytes.drop _).take _ = _
  simp only [JFx_NativeBytes.proofBytes,List.drop_append,List.take_append,List.length_append,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof01.bytes,JFx_DataProof01.c00_length,JFx_DataProof01.c01_length,JFx_DataProof01.c02_length,JFx_DataProof01.c03_length,JFx_DataProof01.c04_length,JFx_DataProof01.c05_length,JFx_DataProof01.c06_length,JFx_DataProof01.c07_length,JFx_DataProof01.c08_length,JFx_DataProof01.c09_length,JFx_DataProof01.c10_length,JFx_DataProof01.c11_length,JFx_DataProof01.c12_length,JFx_DataProof01.c13_length,JFx_DataProof01.c14_length,JFx_DataProof01.c15_length,JFx_DataProof01.c16_length,JFx_DataProof01.c17_length,JFx_DataProof01.c18_length,JFx_DataProof01.c19_length,JFx_DataProof01.c20_length,JFx_DataProof01.c21_length,JFx_DataProof01.c22_length,JFx_DataProof01.c23_length,JFx_DataProof01.c24_length,JFx_DataProof01.c25_length,JFx_DataProof01.c26_length,JFx_DataProof01.c27_length,JFx_DataProof01.c28_length,JFx_DataProof01.c29_length,JFx_DataProof01.c30_length,JFx_DataProof01.c31_length,JFx_DataProof01.c32_length,JFx_DataProof01.c33_length,JFx_DataProof01.c34_length,JFx_DataProof01.c35_length,JFx_DataProof01.c36_length,JFx_DataProof01.c37_length,JFx_DataProof01.c38_length,JFx_DataProof01.c39_length,JFx_DataProof01.c40_length,JFx_DataProof01.c41_length,JFx_DataProof01.c42_length,JFx_DataProof01.c43_length,JFx_DataProof01.c44_length,JFx_DataProof01.c45_length,JFx_DataProof01.c46_length,JFx_DataProof01.c47_length,JFx_DataProof01.c48_length,JFx_DataProof01.c49_length,JFx_DataProof01.c50_length,JFx_DataProof01.c51_length,JFx_DataProof01.c52_length,JFx_DataProof01.c53_length,JFx_DataProof01.c54_length,JFx_DataProof01.c55_length,JFx_DataProof01.c56_length,JFx_DataProof01.c57_length,JFx_DataProof01.c58_length,JFx_DataProof01.c59_length,JFx_DataProof01.c60_length,JFx_DataProof01.c61_length,JFx_DataProof01.c62_length,JFx_DataProof01.c63_length,JFx_DataProof01.c64_length,JFx_DataProof01.c65_length,JFx_DataProof01.c66_length,JFx_DataProof01.c67_length,JFx_DataProof01.c68_length,JFx_DataProof01.c69_length,JFx_DataProof01.c70_length,JFx_DataProof01.c71_length,JFx_DataProof01.c72_length,JFx_DataProof01.c73_length,JFx_DataProof01.c74_length,JFx_DataProof01.c75_length,JFx_DataProof01.c76_length,JFx_DataProof01.c77_length,JFx_DataProof01.c78_length,JFx_DataProof01.c79_length,JFx_DataProof01.c80_length,JFx_DataProof01.c81_length,JFx_DataProof01.c82_length,JFx_DataProof01.c83_length,JFx_DataProof01.c84_length,JFx_DataProof01.c85_length,JFx_DataProof01.c86_length,JFx_DataProof01.c87_length,JFx_DataProof01.c88_length,JFx_DataProof01.c89_length,JFx_DataProof01.c90_length,JFx_DataProof01.c91_length,JFx_DataProof01.c92_length,JFx_DataProof01.c93_length,JFx_DataProof01.c94_length,JFx_DataProof01.c95_length,JFx_DataProof01.c96_length,JFx_DataProof01.c97_length,JFx_DataProof01.c98_length,JFx_DataProof01.c99_length,JFx_DataProof01.c100_length,JFx_DataProof01.c101_length,JFx_DataProof01.c102_length,JFx_DataProof01.c103_length,JFx_DataProof01.c104_length,JFx_DataProof01.c105_length,JFx_DataProof01.c106_length,JFx_DataProof01.c107_length,JFx_DataProof01.c108_length,JFx_DataProof01.c109_length,JFx_DataProof01.c110_length,JFx_DataProof01.c111_length,JFx_DataProof01.c112_length,JFx_DataProof01.c113_length,JFx_DataProof01.c114_length,JFx_DataProof01.c115_length,JFx_DataProof01.c116_length,JFx_DataProof01.c117_length,JFx_DataProof01.c118_length,JFx_DataProof01.c119_length,JFx_DataProof01.c120_length,JFx_DataProof01.c121_length,JFx_DataProof01.c122_length,JFx_DataProof01.c123_length,JFx_DataProof01.c124_length,JFx_DataProof01.c125_length,JFx_DataProof01.c126_length,JFx_DataProof01.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms header
theorem shape : rowShape 24 = (2,896) := by norm_num [rowShape]
theorem step (rs : List Bytes)
    (tail : semanticRows 2 25 (slice wire 4701 2330) = some rs) :
    semanticRows 3 24 (slice wire 4248 2783) =
      some (PSem_Rows.expandedRow 24 (slice wire 4248 2783) :: rs) := by
  refine JFz_RowGeometry.forward 2 24 _ rs ?_ ?_ ?_ ?_
  · norm_num only [shape,Prod.snd,if_pos (by decide : 14 ≤ 24)]
    rw [slice,List.length_take,List.length_drop,wire_length]
    decide
  · rw [shape]
    rw [slice_take _ 4248 5 2783 (by decide)]
    simp only [slice,wire,bytesOf, ← List.map_drop, ← List.map_take,header]
    rfl
  · intro compact
    rw [shape]
    change canonical (slice (slice wire 4248 2783) 5 448)
    rw [slice_slice _ 4248 2783 5 448 (by decide)]
    exact JFz_Scan57.canonical_selected
  · norm_num only [shape,Prod.snd,if_pos (by decide : 14 ≤ 24)]
    rw [slice_drop]
    exact tail
#print axioms shape
#print axioms step
end AspisR1.JFz_Row24
end
