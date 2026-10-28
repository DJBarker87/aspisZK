import NDO_JGh_TX2_FrontierHeight16
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_Siblings17
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def k2c140 : Array U8 32#usize := Array.make 32#usize [220#u8,196#u8,233#u8,115#u8,158#u8,7#u8,124#u8,8#u8,46#u8,188#u8,36#u8,235#u8,198#u8,156#u8,139#u8,68#u8,223#u8,130#u8,204#u8,114#u8,37#u8,155#u8,16#u8,71#u8,174#u8,150#u8,102#u8,35#u8,254#u8,100#u8,134#u8,80#u8]
theorem k2c140_selected : ((JGh_TX2_NodeViews.nodes2.val).drop 4480).take 32=k2c140.val := by
  rw [JGh_TX2_NodeViews.values2,JFq_Range.nested _ _ 4800 4480 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof13.bytes,JFx_DataProof13.c00_length,JFx_DataProof13.c01_length,JFx_DataProof13.c02_length,JFx_DataProof13.c03_length,JFx_DataProof13.c04_length,JFx_DataProof13.c05_length,JFx_DataProof13.c06_length,JFx_DataProof13.c07_length,JFx_DataProof13.c08_length,JFx_DataProof13.c09_length,JFx_DataProof13.c10_length,JFx_DataProof13.c11_length,JFx_DataProof13.c12_length,JFx_DataProof13.c13_length,JFx_DataProof13.c14_length,JFx_DataProof13.c15_length,JFx_DataProof13.c16_length,JFx_DataProof13.c17_length,JFx_DataProof13.c18_length,JFx_DataProof13.c19_length,JFx_DataProof13.c20_length,JFx_DataProof13.c21_length,JFx_DataProof13.c22_length,JFx_DataProof13.c23_length,JFx_DataProof13.c24_length,JFx_DataProof13.c25_length,JFx_DataProof13.c26_length,JFx_DataProof13.c27_length,JFx_DataProof13.c28_length,JFx_DataProof13.c29_length,JFx_DataProof13.c30_length,JFx_DataProof13.c31_length,JFx_DataProof13.c32_length,JFx_DataProof13.c33_length,JFx_DataProof13.c34_length,JFx_DataProof13.c35_length,JFx_DataProof13.c36_length,JFx_DataProof13.c37_length,JFx_DataProof13.c38_length,JFx_DataProof13.c39_length,JFx_DataProof13.c40_length,JFx_DataProof13.c41_length,JFx_DataProof13.c42_length,JFx_DataProof13.c43_length,JFx_DataProof13.c44_length,JFx_DataProof13.c45_length,JFx_DataProof13.c46_length,JFx_DataProof13.c47_length,JFx_DataProof13.c48_length,JFx_DataProof13.c49_length,JFx_DataProof13.c50_length,JFx_DataProof13.c51_length,JFx_DataProof13.c52_length,JFx_DataProof13.c53_length,JFx_DataProof13.c54_length,JFx_DataProof13.c55_length,JFx_DataProof13.c56_length,JFx_DataProof13.c57_length,JFx_DataProof13.c58_length,JFx_DataProof13.c59_length,JFx_DataProof13.c60_length,JFx_DataProof13.c61_length,JFx_DataProof13.c62_length,JFx_DataProof13.c63_length,JFx_DataProof13.c64_length,JFx_DataProof13.c65_length,JFx_DataProof13.c66_length,JFx_DataProof13.c67_length,JFx_DataProof13.c68_length,JFx_DataProof13.c69_length,JFx_DataProof13.c70_length,JFx_DataProof13.c71_length,JFx_DataProof13.c72_length,JFx_DataProof13.c73_length,JFx_DataProof13.c74_length,JFx_DataProof13.c75_length,JFx_DataProof13.c76_length,JFx_DataProof13.c77_length,JFx_DataProof13.c78_length,JFx_DataProof13.c79_length,JFx_DataProof13.c80_length,JFx_DataProof13.c81_length,JFx_DataProof13.c82_length,JFx_DataProof13.c83_length,JFx_DataProof13.c84_length,JFx_DataProof13.c85_length,JFx_DataProof13.c86_length,JFx_DataProof13.c87_length,JFx_DataProof13.c88_length,JFx_DataProof13.c89_length,JFx_DataProof13.c90_length,JFx_DataProof13.c91_length,JFx_DataProof13.c92_length,JFx_DataProof13.c93_length,JFx_DataProof13.c94_length,JFx_DataProof13.c95_length,JFx_DataProof13.c96_length,JFx_DataProof13.c97_length,JFx_DataProof13.c98_length,JFx_DataProof13.c99_length,JFx_DataProof13.c100_length,JFx_DataProof13.c101_length,JFx_DataProof13.c102_length,JFx_DataProof13.c103_length,JFx_DataProof13.c104_length,JFx_DataProof13.c105_length,JFx_DataProof13.c106_length,JFx_DataProof13.c107_length,JFx_DataProof13.c108_length,JFx_DataProof13.c109_length,JFx_DataProof13.c110_length,JFx_DataProof13.c111_length,JFx_DataProof13.c112_length,JFx_DataProof13.c113_length,JFx_DataProof13.c114_length,JFx_DataProof13.c115_length,JFx_DataProof13.c116_length,JFx_DataProof13.c117_length,JFx_DataProof13.c118_length,JFx_DataProof13.c119_length,JFx_DataProof13.c120_length,JFx_DataProof13.c121_length,JFx_DataProof13.c122_length,JFx_DataProof13.c123_length,JFx_DataProof13.c124_length,JFx_DataProof13.c125_length,JFx_DataProof13.c126_length,JFx_DataProof13.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms k2c140_selected
theorem k2c140_decode : decodeState k2c140=JGc_TX2_M2Roots.siblingAt 17 131072 := by
  funext i
  fin_cases i <;> rfl
#print axioms k2c140_decode
theorem count0_frontier : OraclePortFrozenOrder.countLevel JGf_TX2_Count0.indices17.length JGf_TX2_Count0.indices17=(JGf_TX2_Count0.indices18,0) := by
  rw [←MultiproofConeCountGroups.source_level_eq _ _ (by decide : JGf_TX2_Count0.indices17.Pairwise (·<·))]
  exact JGf_TX2_Count0.level17
#print axioms count0_frontier
theorem count2_frontier : OraclePortFrozenOrder.countLevel JGf_TX2_Count2.indices17.length JGf_TX2_Count2.indices17=(JGf_TX2_Count2.indices18,1) := by
  rw [←MultiproofConeCountGroups.source_level_eq _ _ (by decide : JGf_TX2_Count2.indices17.Pairwise (·<·))]
  exact JGf_TX2_Count2.level17
#print axioms count2_frontier
theorem k2c140_read : JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes2 140=JGc_TX2_M2Roots.siblingAt 17 131072 := by
  have selected := JGh_TX2_NodeViews.read_selected JGh_TX2_NodeViews.nodes2 140 k2c140 k2c140_selected
  exact selected.trans k2c140_decode
#print axioms k2c140_read
end AspisR1.JGh_TX2_Siblings17
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_Frontiers
open OraclePortSelectedDraft OracleDecisionMultiBuild
def coords0_185 : List (Nat×Nat) := coords0_183++coords0_184
theorem front0_185 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 18 0=coords0_185 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 18 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [front0_183,front0_184]
  rfl
#print axioms front0_185
def coords2_163 : List (Nat×Nat) := coords2_162++[( 17,131072)]
theorem front2_163 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 18 0=coords2_163 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 18 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [front2_162,unoccupied JGc_TX2_M2Roots.indices 17 131072 (by decide)]
  rfl
#print axioms front2_163
end AspisR1.JGh_TX2_Frontiers
end
