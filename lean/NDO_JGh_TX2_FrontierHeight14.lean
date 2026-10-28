import NDO_JGh_TX2_FrontierHeight13
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_Siblings14
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def k0c160 : Array U8 32#usize := Array.make 32#usize [14#u8,249#u8,49#u8,194#u8,64#u8,5#u8,0#u8,211#u8,197#u8,83#u8,60#u8,63#u8,49#u8,164#u8,189#u8,6#u8,250#u8,112#u8,37#u8,238#u8,152#u8,152#u8,223#u8,179#u8,110#u8,114#u8,244#u8,152#u8,9#u8,157#u8,125#u8,189#u8]
theorem k0c160_selected : ((JGh_TX2_NodeViews.nodes0.val).drop 5120).take 32=k0c160.val := by
  rw [JGh_TX2_NodeViews.values0,JFq_Range.nested _ _ 5504 5120 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof11.bytes,JFx_DataProof11.c00_length,JFx_DataProof11.c01_length,JFx_DataProof11.c02_length,JFx_DataProof11.c03_length,JFx_DataProof11.c04_length,JFx_DataProof11.c05_length,JFx_DataProof11.c06_length,JFx_DataProof11.c07_length,JFx_DataProof11.c08_length,JFx_DataProof11.c09_length,JFx_DataProof11.c10_length,JFx_DataProof11.c11_length,JFx_DataProof11.c12_length,JFx_DataProof11.c13_length,JFx_DataProof11.c14_length,JFx_DataProof11.c15_length,JFx_DataProof11.c16_length,JFx_DataProof11.c17_length,JFx_DataProof11.c18_length,JFx_DataProof11.c19_length,JFx_DataProof11.c20_length,JFx_DataProof11.c21_length,JFx_DataProof11.c22_length,JFx_DataProof11.c23_length,JFx_DataProof11.c24_length,JFx_DataProof11.c25_length,JFx_DataProof11.c26_length,JFx_DataProof11.c27_length,JFx_DataProof11.c28_length,JFx_DataProof11.c29_length,JFx_DataProof11.c30_length,JFx_DataProof11.c31_length,JFx_DataProof11.c32_length,JFx_DataProof11.c33_length,JFx_DataProof11.c34_length,JFx_DataProof11.c35_length,JFx_DataProof11.c36_length,JFx_DataProof11.c37_length,JFx_DataProof11.c38_length,JFx_DataProof11.c39_length,JFx_DataProof11.c40_length,JFx_DataProof11.c41_length,JFx_DataProof11.c42_length,JFx_DataProof11.c43_length,JFx_DataProof11.c44_length,JFx_DataProof11.c45_length,JFx_DataProof11.c46_length,JFx_DataProof11.c47_length,JFx_DataProof11.c48_length,JFx_DataProof11.c49_length,JFx_DataProof11.c50_length,JFx_DataProof11.c51_length,JFx_DataProof11.c52_length,JFx_DataProof11.c53_length,JFx_DataProof11.c54_length,JFx_DataProof11.c55_length,JFx_DataProof11.c56_length,JFx_DataProof11.c57_length,JFx_DataProof11.c58_length,JFx_DataProof11.c59_length,JFx_DataProof11.c60_length,JFx_DataProof11.c61_length,JFx_DataProof11.c62_length,JFx_DataProof11.c63_length,JFx_DataProof11.c64_length,JFx_DataProof11.c65_length,JFx_DataProof11.c66_length,JFx_DataProof11.c67_length,JFx_DataProof11.c68_length,JFx_DataProof11.c69_length,JFx_DataProof11.c70_length,JFx_DataProof11.c71_length,JFx_DataProof11.c72_length,JFx_DataProof11.c73_length,JFx_DataProof11.c74_length,JFx_DataProof11.c75_length,JFx_DataProof11.c76_length,JFx_DataProof11.c77_length,JFx_DataProof11.c78_length,JFx_DataProof11.c79_length,JFx_DataProof11.c80_length,JFx_DataProof11.c81_length,JFx_DataProof11.c82_length,JFx_DataProof11.c83_length,JFx_DataProof11.c84_length,JFx_DataProof11.c85_length,JFx_DataProof11.c86_length,JFx_DataProof11.c87_length,JFx_DataProof11.c88_length,JFx_DataProof11.c89_length,JFx_DataProof11.c90_length,JFx_DataProof11.c91_length,JFx_DataProof11.c92_length,JFx_DataProof11.c93_length,JFx_DataProof11.c94_length,JFx_DataProof11.c95_length,JFx_DataProof11.c96_length,JFx_DataProof11.c97_length,JFx_DataProof11.c98_length,JFx_DataProof11.c99_length,JFx_DataProof11.c100_length,JFx_DataProof11.c101_length,JFx_DataProof11.c102_length,JFx_DataProof11.c103_length,JFx_DataProof11.c104_length,JFx_DataProof11.c105_length,JFx_DataProof11.c106_length,JFx_DataProof11.c107_length,JFx_DataProof11.c108_length,JFx_DataProof11.c109_length,JFx_DataProof11.c110_length,JFx_DataProof11.c111_length,JFx_DataProof11.c112_length,JFx_DataProof11.c113_length,JFx_DataProof11.c114_length,JFx_DataProof11.c115_length,JFx_DataProof11.c116_length,JFx_DataProof11.c117_length,JFx_DataProof11.c118_length,JFx_DataProof11.c119_length,JFx_DataProof11.c120_length,JFx_DataProof11.c121_length,JFx_DataProof11.c122_length,JFx_DataProof11.c123_length,JFx_DataProof11.c124_length,JFx_DataProof11.c125_length,JFx_DataProof11.c126_length,JFx_DataProof11.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms k0c160_selected
theorem k0c160_decode : decodeState k0c160=JGf_TX2_M0Roots.siblingAt 14 196608 := by
  funext i
  fin_cases i <;> rfl
#print axioms k0c160_decode
def k1c160 : Array U8 32#usize := Array.make 32#usize [94#u8,141#u8,123#u8,142#u8,16#u8,86#u8,40#u8,121#u8,91#u8,237#u8,183#u8,116#u8,254#u8,58#u8,142#u8,124#u8,219#u8,39#u8,123#u8,41#u8,165#u8,187#u8,42#u8,68#u8,243#u8,146#u8,139#u8,31#u8,5#u8,160#u8,3#u8,117#u8]
theorem k1c160_selected : ((JGh_TX2_NodeViews.nodes1.val).drop 5120).take 32=k1c160.val := by
  rw [JGh_TX2_NodeViews.values1,JFq_Range.nested _ _ 5504 5120 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof12.bytes,JFx_DataProof12.c00_length,JFx_DataProof12.c01_length,JFx_DataProof12.c02_length,JFx_DataProof12.c03_length,JFx_DataProof12.c04_length,JFx_DataProof12.c05_length,JFx_DataProof12.c06_length,JFx_DataProof12.c07_length,JFx_DataProof12.c08_length,JFx_DataProof12.c09_length,JFx_DataProof12.c10_length,JFx_DataProof12.c11_length,JFx_DataProof12.c12_length,JFx_DataProof12.c13_length,JFx_DataProof12.c14_length,JFx_DataProof12.c15_length,JFx_DataProof12.c16_length,JFx_DataProof12.c17_length,JFx_DataProof12.c18_length,JFx_DataProof12.c19_length,JFx_DataProof12.c20_length,JFx_DataProof12.c21_length,JFx_DataProof12.c22_length,JFx_DataProof12.c23_length,JFx_DataProof12.c24_length,JFx_DataProof12.c25_length,JFx_DataProof12.c26_length,JFx_DataProof12.c27_length,JFx_DataProof12.c28_length,JFx_DataProof12.c29_length,JFx_DataProof12.c30_length,JFx_DataProof12.c31_length,JFx_DataProof12.c32_length,JFx_DataProof12.c33_length,JFx_DataProof12.c34_length,JFx_DataProof12.c35_length,JFx_DataProof12.c36_length,JFx_DataProof12.c37_length,JFx_DataProof12.c38_length,JFx_DataProof12.c39_length,JFx_DataProof12.c40_length,JFx_DataProof12.c41_length,JFx_DataProof12.c42_length,JFx_DataProof12.c43_length,JFx_DataProof12.c44_length,JFx_DataProof12.c45_length,JFx_DataProof12.c46_length,JFx_DataProof12.c47_length,JFx_DataProof12.c48_length,JFx_DataProof12.c49_length,JFx_DataProof12.c50_length,JFx_DataProof12.c51_length,JFx_DataProof12.c52_length,JFx_DataProof12.c53_length,JFx_DataProof12.c54_length,JFx_DataProof12.c55_length,JFx_DataProof12.c56_length,JFx_DataProof12.c57_length,JFx_DataProof12.c58_length,JFx_DataProof12.c59_length,JFx_DataProof12.c60_length,JFx_DataProof12.c61_length,JFx_DataProof12.c62_length,JFx_DataProof12.c63_length,JFx_DataProof12.c64_length,JFx_DataProof12.c65_length,JFx_DataProof12.c66_length,JFx_DataProof12.c67_length,JFx_DataProof12.c68_length,JFx_DataProof12.c69_length,JFx_DataProof12.c70_length,JFx_DataProof12.c71_length,JFx_DataProof12.c72_length,JFx_DataProof12.c73_length,JFx_DataProof12.c74_length,JFx_DataProof12.c75_length,JFx_DataProof12.c76_length,JFx_DataProof12.c77_length,JFx_DataProof12.c78_length,JFx_DataProof12.c79_length,JFx_DataProof12.c80_length,JFx_DataProof12.c81_length,JFx_DataProof12.c82_length,JFx_DataProof12.c83_length,JFx_DataProof12.c84_length,JFx_DataProof12.c85_length,JFx_DataProof12.c86_length,JFx_DataProof12.c87_length,JFx_DataProof12.c88_length,JFx_DataProof12.c89_length,JFx_DataProof12.c90_length,JFx_DataProof12.c91_length,JFx_DataProof12.c92_length,JFx_DataProof12.c93_length,JFx_DataProof12.c94_length,JFx_DataProof12.c95_length,JFx_DataProof12.c96_length,JFx_DataProof12.c97_length,JFx_DataProof12.c98_length,JFx_DataProof12.c99_length,JFx_DataProof12.c100_length,JFx_DataProof12.c101_length,JFx_DataProof12.c102_length,JFx_DataProof12.c103_length,JFx_DataProof12.c104_length,JFx_DataProof12.c105_length,JFx_DataProof12.c106_length,JFx_DataProof12.c107_length,JFx_DataProof12.c108_length,JFx_DataProof12.c109_length,JFx_DataProof12.c110_length,JFx_DataProof12.c111_length,JFx_DataProof12.c112_length,JFx_DataProof12.c113_length,JFx_DataProof12.c114_length,JFx_DataProof12.c115_length,JFx_DataProof12.c116_length,JFx_DataProof12.c117_length,JFx_DataProof12.c118_length,JFx_DataProof12.c119_length,JFx_DataProof12.c120_length,JFx_DataProof12.c121_length,JFx_DataProof12.c122_length,JFx_DataProof12.c123_length,JFx_DataProof12.c124_length,JFx_DataProof12.c125_length,JFx_DataProof12.c126_length,JFx_DataProof12.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms k1c160_selected
theorem k1c160_decode : decodeState k1c160=JGh_TX2_M1Roots.siblingAt 14 196608 := by
  funext i
  fin_cases i <;> rfl
#print axioms k1c160_decode
def k2c138 : Array U8 32#usize := Array.make 32#usize [228#u8,96#u8,201#u8,65#u8,47#u8,217#u8,114#u8,210#u8,72#u8,6#u8,233#u8,71#u8,93#u8,13#u8,177#u8,139#u8,113#u8,68#u8,25#u8,125#u8,252#u8,162#u8,191#u8,55#u8,162#u8,47#u8,84#u8,136#u8,175#u8,38#u8,253#u8,181#u8]
theorem k2c138_selected : ((JGh_TX2_NodeViews.nodes2.val).drop 4416).take 32=k2c138.val := by
  rw [JGh_TX2_NodeViews.values2,JFq_Range.nested _ _ 4800 4416 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof13.bytes,JFx_DataProof13.c00_length,JFx_DataProof13.c01_length,JFx_DataProof13.c02_length,JFx_DataProof13.c03_length,JFx_DataProof13.c04_length,JFx_DataProof13.c05_length,JFx_DataProof13.c06_length,JFx_DataProof13.c07_length,JFx_DataProof13.c08_length,JFx_DataProof13.c09_length,JFx_DataProof13.c10_length,JFx_DataProof13.c11_length,JFx_DataProof13.c12_length,JFx_DataProof13.c13_length,JFx_DataProof13.c14_length,JFx_DataProof13.c15_length,JFx_DataProof13.c16_length,JFx_DataProof13.c17_length,JFx_DataProof13.c18_length,JFx_DataProof13.c19_length,JFx_DataProof13.c20_length,JFx_DataProof13.c21_length,JFx_DataProof13.c22_length,JFx_DataProof13.c23_length,JFx_DataProof13.c24_length,JFx_DataProof13.c25_length,JFx_DataProof13.c26_length,JFx_DataProof13.c27_length,JFx_DataProof13.c28_length,JFx_DataProof13.c29_length,JFx_DataProof13.c30_length,JFx_DataProof13.c31_length,JFx_DataProof13.c32_length,JFx_DataProof13.c33_length,JFx_DataProof13.c34_length,JFx_DataProof13.c35_length,JFx_DataProof13.c36_length,JFx_DataProof13.c37_length,JFx_DataProof13.c38_length,JFx_DataProof13.c39_length,JFx_DataProof13.c40_length,JFx_DataProof13.c41_length,JFx_DataProof13.c42_length,JFx_DataProof13.c43_length,JFx_DataProof13.c44_length,JFx_DataProof13.c45_length,JFx_DataProof13.c46_length,JFx_DataProof13.c47_length,JFx_DataProof13.c48_length,JFx_DataProof13.c49_length,JFx_DataProof13.c50_length,JFx_DataProof13.c51_length,JFx_DataProof13.c52_length,JFx_DataProof13.c53_length,JFx_DataProof13.c54_length,JFx_DataProof13.c55_length,JFx_DataProof13.c56_length,JFx_DataProof13.c57_length,JFx_DataProof13.c58_length,JFx_DataProof13.c59_length,JFx_DataProof13.c60_length,JFx_DataProof13.c61_length,JFx_DataProof13.c62_length,JFx_DataProof13.c63_length,JFx_DataProof13.c64_length,JFx_DataProof13.c65_length,JFx_DataProof13.c66_length,JFx_DataProof13.c67_length,JFx_DataProof13.c68_length,JFx_DataProof13.c69_length,JFx_DataProof13.c70_length,JFx_DataProof13.c71_length,JFx_DataProof13.c72_length,JFx_DataProof13.c73_length,JFx_DataProof13.c74_length,JFx_DataProof13.c75_length,JFx_DataProof13.c76_length,JFx_DataProof13.c77_length,JFx_DataProof13.c78_length,JFx_DataProof13.c79_length,JFx_DataProof13.c80_length,JFx_DataProof13.c81_length,JFx_DataProof13.c82_length,JFx_DataProof13.c83_length,JFx_DataProof13.c84_length,JFx_DataProof13.c85_length,JFx_DataProof13.c86_length,JFx_DataProof13.c87_length,JFx_DataProof13.c88_length,JFx_DataProof13.c89_length,JFx_DataProof13.c90_length,JFx_DataProof13.c91_length,JFx_DataProof13.c92_length,JFx_DataProof13.c93_length,JFx_DataProof13.c94_length,JFx_DataProof13.c95_length,JFx_DataProof13.c96_length,JFx_DataProof13.c97_length,JFx_DataProof13.c98_length,JFx_DataProof13.c99_length,JFx_DataProof13.c100_length,JFx_DataProof13.c101_length,JFx_DataProof13.c102_length,JFx_DataProof13.c103_length,JFx_DataProof13.c104_length,JFx_DataProof13.c105_length,JFx_DataProof13.c106_length,JFx_DataProof13.c107_length,JFx_DataProof13.c108_length,JFx_DataProof13.c109_length,JFx_DataProof13.c110_length,JFx_DataProof13.c111_length,JFx_DataProof13.c112_length,JFx_DataProof13.c113_length,JFx_DataProof13.c114_length,JFx_DataProof13.c115_length,JFx_DataProof13.c116_length,JFx_DataProof13.c117_length,JFx_DataProof13.c118_length,JFx_DataProof13.c119_length,JFx_DataProof13.c120_length,JFx_DataProof13.c121_length,JFx_DataProof13.c122_length,JFx_DataProof13.c123_length,JFx_DataProof13.c124_length,JFx_DataProof13.c125_length,JFx_DataProof13.c126_length,JFx_DataProof13.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms k2c138_selected
theorem k2c138_decode : decodeState k2c138=JGc_TX2_M2Roots.siblingAt 14 16384 := by
  funext i
  fin_cases i <;> rfl
#print axioms k2c138_decode
theorem count0_frontier : OraclePortFrozenOrder.countLevel JGf_TX2_Count0.indices14.length JGf_TX2_Count0.indices14=(JGf_TX2_Count0.indices15,1) := by
  rw [←MultiproofConeCountGroups.source_level_eq _ _ (by decide : JGf_TX2_Count0.indices14.Pairwise (·<·))]
  exact JGf_TX2_Count0.level14
#print axioms count0_frontier
theorem count2_frontier : OraclePortFrozenOrder.countLevel JGf_TX2_Count2.indices14.length JGf_TX2_Count2.indices14=(JGf_TX2_Count2.indices15,1) := by
  rw [←MultiproofConeCountGroups.source_level_eq _ _ (by decide : JGf_TX2_Count2.indices14.Pairwise (·<·))]
  exact JGf_TX2_Count2.level14
#print axioms count2_frontier
theorem k0c160_read : JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes0 160=JGf_TX2_M0Roots.siblingAt 14 196608 := by
  have selected := JGh_TX2_NodeViews.read_selected JGh_TX2_NodeViews.nodes0 160 k0c160 k0c160_selected
  exact selected.trans k0c160_decode
#print axioms k0c160_read
theorem k1c160_read : JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes1 160=JGh_TX2_M1Roots.siblingAt 14 196608 := by
  have selected := JGh_TX2_NodeViews.read_selected JGh_TX2_NodeViews.nodes1 160 k1c160 k1c160_selected
  exact selected.trans k1c160_decode
#print axioms k1c160_read
theorem k2c138_read : JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes2 138=JGc_TX2_M2Roots.siblingAt 14 16384 := by
  have selected := JGh_TX2_NodeViews.read_selected JGh_TX2_NodeViews.nodes2 138 k2c138 k2c138_selected
  exact selected.trans k2c138_decode
#print axioms k2c138_read
end AspisR1.JGh_TX2_Siblings14
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_Frontiers
open OraclePortSelectedDraft OracleDecisionMultiBuild
def coords0_175 : List (Nat×Nat) := coords0_166++coords0_167
theorem front0_175 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 15 0=coords0_175 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 15 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [front0_166,front0_167]
  rfl
#print axioms front0_175
def coords0_176 : List (Nat×Nat) := coords0_168++coords0_169
theorem front0_176 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 15 32768=coords0_176 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 15 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [front0_168,front0_169]
  rfl
#print axioms front0_176
def coords0_177 : List (Nat×Nat) := coords0_170++coords0_171
theorem front0_177 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 15 131072=coords0_177 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 15 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [front0_170,front0_171]
  rfl
#print axioms front0_177
def coords0_178 : List (Nat×Nat) := coords0_172++coords0_173
theorem front0_178 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 15 163840=coords0_178 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 15 163840)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [front0_172,front0_173]
  rfl
#print axioms front0_178
def coords0_179 : List (Nat×Nat) := [( 14,196608)]++coords0_174
theorem front0_179 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 15 196608=coords0_179 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 15 196608)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied JGf_TX2_M0Roots.indices 14 196608 (by decide),front0_174]
  rfl
#print axioms front0_179
def coords2_159 : List (Nat×Nat) := coords2_156++[( 14,16384)]
theorem front2_159 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 15 0=coords2_159 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 15 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [front2_156,unoccupied JGc_TX2_M2Roots.indices 14 16384 (by decide)]
  rfl
#print axioms front2_159
def coords2_160 : List (Nat×Nat) := coords2_157++coords2_158
theorem front2_160 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 15 32768=coords2_160 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 15 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [front2_157,front2_158]
  rfl
#print axioms front2_160
end AspisR1.JGh_TX2_Frontiers
end
