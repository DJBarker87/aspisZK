import NDO_JGh_TX2_FrontierHeight14
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_Siblings15
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def k0c161 : Array U8 32#usize := Array.make 32#usize [78#u8,76#u8,78#u8,145#u8,83#u8,145#u8,125#u8,165#u8,149#u8,199#u8,20#u8,232#u8,15#u8,8#u8,165#u8,94#u8,236#u8,114#u8,212#u8,6#u8,118#u8,28#u8,230#u8,173#u8,255#u8,46#u8,190#u8,216#u8,0#u8,213#u8,150#u8,249#u8]
theorem k0c161_selected : ((JGh_TX2_NodeViews.nodes0.val).drop 5152).take 32=k0c161.val := by
  rw [JGh_TX2_NodeViews.values0,JFq_Range.nested _ _ 5504 5152 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof11.bytes,JFx_DataProof11.c00_length,JFx_DataProof11.c01_length,JFx_DataProof11.c02_length,JFx_DataProof11.c03_length,JFx_DataProof11.c04_length,JFx_DataProof11.c05_length,JFx_DataProof11.c06_length,JFx_DataProof11.c07_length,JFx_DataProof11.c08_length,JFx_DataProof11.c09_length,JFx_DataProof11.c10_length,JFx_DataProof11.c11_length,JFx_DataProof11.c12_length,JFx_DataProof11.c13_length,JFx_DataProof11.c14_length,JFx_DataProof11.c15_length,JFx_DataProof11.c16_length,JFx_DataProof11.c17_length,JFx_DataProof11.c18_length,JFx_DataProof11.c19_length,JFx_DataProof11.c20_length,JFx_DataProof11.c21_length,JFx_DataProof11.c22_length,JFx_DataProof11.c23_length,JFx_DataProof11.c24_length,JFx_DataProof11.c25_length,JFx_DataProof11.c26_length,JFx_DataProof11.c27_length,JFx_DataProof11.c28_length,JFx_DataProof11.c29_length,JFx_DataProof11.c30_length,JFx_DataProof11.c31_length,JFx_DataProof11.c32_length,JFx_DataProof11.c33_length,JFx_DataProof11.c34_length,JFx_DataProof11.c35_length,JFx_DataProof11.c36_length,JFx_DataProof11.c37_length,JFx_DataProof11.c38_length,JFx_DataProof11.c39_length,JFx_DataProof11.c40_length,JFx_DataProof11.c41_length,JFx_DataProof11.c42_length,JFx_DataProof11.c43_length,JFx_DataProof11.c44_length,JFx_DataProof11.c45_length,JFx_DataProof11.c46_length,JFx_DataProof11.c47_length,JFx_DataProof11.c48_length,JFx_DataProof11.c49_length,JFx_DataProof11.c50_length,JFx_DataProof11.c51_length,JFx_DataProof11.c52_length,JFx_DataProof11.c53_length,JFx_DataProof11.c54_length,JFx_DataProof11.c55_length,JFx_DataProof11.c56_length,JFx_DataProof11.c57_length,JFx_DataProof11.c58_length,JFx_DataProof11.c59_length,JFx_DataProof11.c60_length,JFx_DataProof11.c61_length,JFx_DataProof11.c62_length,JFx_DataProof11.c63_length,JFx_DataProof11.c64_length,JFx_DataProof11.c65_length,JFx_DataProof11.c66_length,JFx_DataProof11.c67_length,JFx_DataProof11.c68_length,JFx_DataProof11.c69_length,JFx_DataProof11.c70_length,JFx_DataProof11.c71_length,JFx_DataProof11.c72_length,JFx_DataProof11.c73_length,JFx_DataProof11.c74_length,JFx_DataProof11.c75_length,JFx_DataProof11.c76_length,JFx_DataProof11.c77_length,JFx_DataProof11.c78_length,JFx_DataProof11.c79_length,JFx_DataProof11.c80_length,JFx_DataProof11.c81_length,JFx_DataProof11.c82_length,JFx_DataProof11.c83_length,JFx_DataProof11.c84_length,JFx_DataProof11.c85_length,JFx_DataProof11.c86_length,JFx_DataProof11.c87_length,JFx_DataProof11.c88_length,JFx_DataProof11.c89_length,JFx_DataProof11.c90_length,JFx_DataProof11.c91_length,JFx_DataProof11.c92_length,JFx_DataProof11.c93_length,JFx_DataProof11.c94_length,JFx_DataProof11.c95_length,JFx_DataProof11.c96_length,JFx_DataProof11.c97_length,JFx_DataProof11.c98_length,JFx_DataProof11.c99_length,JFx_DataProof11.c100_length,JFx_DataProof11.c101_length,JFx_DataProof11.c102_length,JFx_DataProof11.c103_length,JFx_DataProof11.c104_length,JFx_DataProof11.c105_length,JFx_DataProof11.c106_length,JFx_DataProof11.c107_length,JFx_DataProof11.c108_length,JFx_DataProof11.c109_length,JFx_DataProof11.c110_length,JFx_DataProof11.c111_length,JFx_DataProof11.c112_length,JFx_DataProof11.c113_length,JFx_DataProof11.c114_length,JFx_DataProof11.c115_length,JFx_DataProof11.c116_length,JFx_DataProof11.c117_length,JFx_DataProof11.c118_length,JFx_DataProof11.c119_length,JFx_DataProof11.c120_length,JFx_DataProof11.c121_length,JFx_DataProof11.c122_length,JFx_DataProof11.c123_length,JFx_DataProof11.c124_length,JFx_DataProof11.c125_length,JFx_DataProof11.c126_length,JFx_DataProof11.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms k0c161_selected
theorem k0c161_decode : decodeState k0c161=JGf_TX2_M0Roots.siblingAt 15 229376 := by
  funext i
  fin_cases i <;> rfl
#print axioms k0c161_decode
def k1c161 : Array U8 32#usize := Array.make 32#usize [182#u8,200#u8,136#u8,128#u8,28#u8,103#u8,243#u8,43#u8,124#u8,178#u8,179#u8,200#u8,233#u8,131#u8,66#u8,8#u8,228#u8,100#u8,70#u8,152#u8,221#u8,121#u8,91#u8,5#u8,60#u8,103#u8,251#u8,148#u8,164#u8,131#u8,164#u8,56#u8]
theorem k1c161_selected : ((JGh_TX2_NodeViews.nodes1.val).drop 5152).take 32=k1c161.val := by
  rw [JGh_TX2_NodeViews.values1,JFq_Range.nested _ _ 5504 5152 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof12.bytes,JFx_DataProof12.c00_length,JFx_DataProof12.c01_length,JFx_DataProof12.c02_length,JFx_DataProof12.c03_length,JFx_DataProof12.c04_length,JFx_DataProof12.c05_length,JFx_DataProof12.c06_length,JFx_DataProof12.c07_length,JFx_DataProof12.c08_length,JFx_DataProof12.c09_length,JFx_DataProof12.c10_length,JFx_DataProof12.c11_length,JFx_DataProof12.c12_length,JFx_DataProof12.c13_length,JFx_DataProof12.c14_length,JFx_DataProof12.c15_length,JFx_DataProof12.c16_length,JFx_DataProof12.c17_length,JFx_DataProof12.c18_length,JFx_DataProof12.c19_length,JFx_DataProof12.c20_length,JFx_DataProof12.c21_length,JFx_DataProof12.c22_length,JFx_DataProof12.c23_length,JFx_DataProof12.c24_length,JFx_DataProof12.c25_length,JFx_DataProof12.c26_length,JFx_DataProof12.c27_length,JFx_DataProof12.c28_length,JFx_DataProof12.c29_length,JFx_DataProof12.c30_length,JFx_DataProof12.c31_length,JFx_DataProof12.c32_length,JFx_DataProof12.c33_length,JFx_DataProof12.c34_length,JFx_DataProof12.c35_length,JFx_DataProof12.c36_length,JFx_DataProof12.c37_length,JFx_DataProof12.c38_length,JFx_DataProof12.c39_length,JFx_DataProof12.c40_length,JFx_DataProof12.c41_length,JFx_DataProof12.c42_length,JFx_DataProof12.c43_length,JFx_DataProof12.c44_length,JFx_DataProof12.c45_length,JFx_DataProof12.c46_length,JFx_DataProof12.c47_length,JFx_DataProof12.c48_length,JFx_DataProof12.c49_length,JFx_DataProof12.c50_length,JFx_DataProof12.c51_length,JFx_DataProof12.c52_length,JFx_DataProof12.c53_length,JFx_DataProof12.c54_length,JFx_DataProof12.c55_length,JFx_DataProof12.c56_length,JFx_DataProof12.c57_length,JFx_DataProof12.c58_length,JFx_DataProof12.c59_length,JFx_DataProof12.c60_length,JFx_DataProof12.c61_length,JFx_DataProof12.c62_length,JFx_DataProof12.c63_length,JFx_DataProof12.c64_length,JFx_DataProof12.c65_length,JFx_DataProof12.c66_length,JFx_DataProof12.c67_length,JFx_DataProof12.c68_length,JFx_DataProof12.c69_length,JFx_DataProof12.c70_length,JFx_DataProof12.c71_length,JFx_DataProof12.c72_length,JFx_DataProof12.c73_length,JFx_DataProof12.c74_length,JFx_DataProof12.c75_length,JFx_DataProof12.c76_length,JFx_DataProof12.c77_length,JFx_DataProof12.c78_length,JFx_DataProof12.c79_length,JFx_DataProof12.c80_length,JFx_DataProof12.c81_length,JFx_DataProof12.c82_length,JFx_DataProof12.c83_length,JFx_DataProof12.c84_length,JFx_DataProof12.c85_length,JFx_DataProof12.c86_length,JFx_DataProof12.c87_length,JFx_DataProof12.c88_length,JFx_DataProof12.c89_length,JFx_DataProof12.c90_length,JFx_DataProof12.c91_length,JFx_DataProof12.c92_length,JFx_DataProof12.c93_length,JFx_DataProof12.c94_length,JFx_DataProof12.c95_length,JFx_DataProof12.c96_length,JFx_DataProof12.c97_length,JFx_DataProof12.c98_length,JFx_DataProof12.c99_length,JFx_DataProof12.c100_length,JFx_DataProof12.c101_length,JFx_DataProof12.c102_length,JFx_DataProof12.c103_length,JFx_DataProof12.c104_length,JFx_DataProof12.c105_length,JFx_DataProof12.c106_length,JFx_DataProof12.c107_length,JFx_DataProof12.c108_length,JFx_DataProof12.c109_length,JFx_DataProof12.c110_length,JFx_DataProof12.c111_length,JFx_DataProof12.c112_length,JFx_DataProof12.c113_length,JFx_DataProof12.c114_length,JFx_DataProof12.c115_length,JFx_DataProof12.c116_length,JFx_DataProof12.c117_length,JFx_DataProof12.c118_length,JFx_DataProof12.c119_length,JFx_DataProof12.c120_length,JFx_DataProof12.c121_length,JFx_DataProof12.c122_length,JFx_DataProof12.c123_length,JFx_DataProof12.c124_length,JFx_DataProof12.c125_length,JFx_DataProof12.c126_length,JFx_DataProof12.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms k1c161_selected
theorem k1c161_decode : decodeState k1c161=JGh_TX2_M1Roots.siblingAt 15 229376 := by
  funext i
  fin_cases i <;> rfl
#print axioms k1c161_decode
theorem count0_frontier : OraclePortFrozenOrder.countLevel JGf_TX2_Count0.indices15.length JGf_TX2_Count0.indices15=(JGf_TX2_Count0.indices16,1) := by
  rw [←MultiproofConeCountGroups.source_level_eq _ _ (by decide : JGf_TX2_Count0.indices15.Pairwise (·<·))]
  exact JGf_TX2_Count0.level15
#print axioms count0_frontier
theorem count2_frontier : OraclePortFrozenOrder.countLevel JGf_TX2_Count2.indices15.length JGf_TX2_Count2.indices15=(JGf_TX2_Count2.indices16,0) := by
  rw [←MultiproofConeCountGroups.source_level_eq _ _ (by decide : JGf_TX2_Count2.indices15.Pairwise (·<·))]
  exact JGf_TX2_Count2.level15
#print axioms count2_frontier
theorem k0c161_read : JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes0 161=JGf_TX2_M0Roots.siblingAt 15 229376 := by
  have selected := JGh_TX2_NodeViews.read_selected JGh_TX2_NodeViews.nodes0 161 k0c161 k0c161_selected
  exact selected.trans k0c161_decode
#print axioms k0c161_read
theorem k1c161_read : JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes1 161=JGh_TX2_M1Roots.siblingAt 15 229376 := by
  have selected := JGh_TX2_NodeViews.read_selected JGh_TX2_NodeViews.nodes1 161 k1c161 k1c161_selected
  exact selected.trans k1c161_decode
#print axioms k1c161_read
end AspisR1.JGh_TX2_Siblings15
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_Frontiers
open OraclePortSelectedDraft OracleDecisionMultiBuild
def coords0_180 : List (Nat×Nat) := coords0_175++coords0_176
theorem front0_180 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 16 0=coords0_180 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 16 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [front0_175,front0_176]
  rfl
#print axioms front0_180
def coords0_181 : List (Nat×Nat) := coords0_177++coords0_178
theorem front0_181 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 16 131072=coords0_181 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 16 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [front0_177,front0_178]
  rfl
#print axioms front0_181
def coords0_182 : List (Nat×Nat) := coords0_179++[( 15,229376)]
theorem front0_182 : OraclePortSelectedDraft.frontier JGf_TX2_M0Roots.indices 16 196608=coords0_182 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGf_TX2_M0Roots.indices 16 196608)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [front0_179,unoccupied JGf_TX2_M0Roots.indices 15 229376 (by decide)]
  rfl
#print axioms front0_182
def coords2_161 : List (Nat×Nat) := coords2_159++coords2_160
theorem front2_161 : OraclePortSelectedDraft.frontier JGc_TX2_M2Roots.indices 16 0=coords2_161 := by
  rw [OraclePortSelectedDraft.frontier,if_pos (by decide : Occupied JGc_TX2_M2Roots.indices 16 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [front2_159,front2_160]
  rfl
#print axioms front2_161
end AspisR1.JGh_TX2_Frontiers
end
