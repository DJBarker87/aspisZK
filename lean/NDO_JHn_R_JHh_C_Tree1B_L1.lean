import NDO_JHn_R_JHh_C_Tree1B_L0
import RPt_JFq_Range
import NDO_JFw_Frames
import NDO_JGm_TX2_View
import NDO_JGp_Opening0
import NDO_JGp_Opening1
import NDO_JGp_Opening2
import NDO_JGp_Opening3
import NDO_JGp_Opening4
import NDO_JGp_Opening5
import NDO_JGp_Opening6
import NDO_JGp_Opening7
import NDO_JGp_Opening8
import NDO_JGp_Opening9
import NDO_JGu_Keys
import NDO_JGy_LightCore
import NDO_JGy_LightPadding
import NDO_JHn_R_JHh_C_Tree1A
import NDO_JHe_SHARealization
import Port4B_KeyDecode
section
variable [sha : AspisR1.JHe_SHARealization]
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_M1Leaf05
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := [204#u8,246#u8,32#u8,71#u8,137#u8,70#u8,172#u8,1#u8,86#u8,141#u8,16#u8,56#u8,13#u8,64#u8,71#u8,125#u8,177#u8,79#u8,230#u8,21#u8,195#u8,114#u8,12#u8,6#u8,9#u8,162#u8,245#u8,123#u8,199#u8,97#u8,255#u8,84#u8]
def n0 : List Nat := [204,246,32,71,137,70,172,1,86,141,16,56,13,64,71,125,177,79,230,21,195,114,12,6,9,162,245,123,199,97,255,84]
theorem cast0 : (c0.map decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
theorem select0 : ((JFo_Opening.value ⟨5,by decide⟩).val.drop 480).take 32=c0 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 480 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select0
def c1 : List U8 := [63#u8,85#u8,247#u8,42#u8,221#u8,251#u8,39#u8,112#u8,212#u8,8#u8,39#u8,48#u8,222#u8,120#u8,21#u8,115#u8,160#u8,109#u8,27#u8,74#u8,186#u8,177#u8,74#u8,98#u8,3#u8,211#u8,148#u8,74#u8,90#u8,17#u8,6#u8,9#u8]
def n1 : List Nat := [63,85,247,42,221,251,39,112,212,8,39,48,222,120,21,115,160,109,27,74,186,177,74,98,3,211,148,74,90,17,6,9]
theorem cast1 : (c1.map decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
theorem select1 : ((JFo_Opening.value ⟨5,by decide⟩).val.drop 512).take 32=c1 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 512 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select1
def c2 : List U8 := [252#u8,64#u8,13#u8,3#u8,211#u8,165#u8,238#u8,98#u8,127#u8,42#u8,93#u8,33#u8,215#u8,75#u8,239#u8,83#u8,71#u8,1#u8,13#u8,42#u8,250#u8,156#u8,89#u8,82#u8,203#u8,118#u8,182#u8,35#u8,220#u8,47#u8,227#u8,103#u8]
def n2 : List Nat := [252,64,13,3,211,165,238,98,127,42,93,33,215,75,239,83,71,1,13,42,250,156,89,82,203,118,182,35,220,47,227,103]
theorem cast2 : (c2.map decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
theorem select2 : ((JFo_Opening.value ⟨5,by decide⟩).val.drop 544).take 32=c2 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 544 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select2
def c3 : List U8 := [24#u8,195#u8,164#u8,123#u8,215#u8,166#u8,91#u8,126#u8,199#u8,148#u8,26#u8,18#u8,128#u8,48#u8,22#u8,55#u8,172#u8,138#u8,230#u8,13#u8,83#u8,193#u8,46#u8,120#u8,49#u8,16#u8,9#u8,49#u8,228#u8,132#u8,182#u8,56#u8]
def n3 : List Nat := [24,195,164,123,215,166,91,126,199,148,26,18,128,48,22,55,172,138,230,13,83,193,46,120,49,16,9,49,228,132,182,56]
theorem cast3 : (c3.map decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
theorem select3 : ((JFo_Opening.value ⟨5,by decide⟩).val.drop 576).take 32=c3 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 576 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select3
def c4 : List U8 := [36#u8,63#u8,188#u8,150#u8,5#u8,14#u8,93#u8,253#u8,218#u8,215#u8,153#u8,119#u8,33#u8,52#u8,10#u8,203#u8,179#u8,162#u8,127#u8,180#u8,47#u8,223#u8,91#u8,99#u8,45#u8,88#u8,35#u8,6#u8,41#u8,228#u8,129#u8,229#u8]
def n4 : List Nat := [36,63,188,150,5,14,93,253,218,215,153,119,33,52,10,203,179,162,127,180,47,223,91,99,45,88,35,6,41,228,129,229]
theorem cast4 : (c4.map decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem select4 : ((JFo_Opening.value ⟨5,by decide⟩).val.drop 640).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 640 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select4
theorem values : ((JFo_Opening.value ⟨5,by decide⟩).val.drop 480).take 128=c0++c1++c2++c3 := by
  have split : ((JFo_Opening.value ⟨5,by decide⟩).val.drop 480).take 128=(((JFo_Opening.value ⟨5,by decide⟩).val.drop 480).drop 0).take 32++(((JFo_Opening.value ⟨5,by decide⟩).val.drop 480).drop 32).take 32++(((JFo_Opening.value ⟨5,by decide⟩).val.drop 480).drop 64).take 32++(((JFo_Opening.value ⟨5,by decide⟩).val.drop 480).drop 96).take 32 := by
    rw [List.take_add (i:=32) (j:=96),List.take_add (i:=32) (j:=64),List.take_add (i:=32) (j:=32)]
    simp only [List.drop_drop,Nat.reduceAdd,List.append_assoc,List.drop_zero]
  simpa only [List.drop_drop,Nat.reduceAdd,select0,select1,select2,select3] using split
#print axioms values
def numeric : List Nat := [16,241]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JHe_C_Gr_M1.Hash005.message := by
  have step0 : [16,241]++n0++n1=JHe_C_Gr_M1.Hash005.B00.input++n1.drop 30 := by rfl
  have h0 : numeric=JHe_C_Gr_M1.Hash005.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have step1 : n1.drop 30++n2++n3=JHe_C_Gr_M1.Hash005.B01.input++n3.drop 30 := by rfl
  have h1 : rest1=JHe_C_Gr_M1.Hash005.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  have tail : rest2=JHe_C_Gr_M1.Hash005.tail := by rfl
  rw [h0,h1,tail]
  simp only [JHe_C_Gr_M1.Hash005.message,JHe_C_Gr_M1.Hash005.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem address : (flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨5,by decide⟩))).map Fin.val=JHe_C_Gr_M1.Hash005.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬1#usize=0#usize),if_pos (by rfl : 1#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨5,by decide⟩) 480#usize 608#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨5,by decide⟩) 640#usize 672#usize).val=c4 := select4
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have htag : (241#u8).val=241 := by scalar_tac
  simpa only [numeric,List.append_assoc,decodeByte,h16,htag] using regroup
#print axioms address
theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 1#usize (JFo_Opening.value ⟨5,by decide⟩)=ok (encodeState JHh_C_Gr_M1Roots.value005) := by
  rw [show Port4B_LeafCode.native _ hash 1#usize (JFo_Opening.value ⟨5,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨5,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨5,by decide⟩)))))=_
  have same : flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨5,by decide⟩))=JHh_C_Gr_M1Roots.input005 :=
    (List.map_inj_right (fun _ _ h => Fin.val_injective h)).mp (address.trans JHh_LeafNumerics1.numeric005.symm)
  rw [same,JHh_C_Gr_M1Roots.hash005]
#print axioms source
end AspisR1.JHh_C_Gu_M1Leaf05
end
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_M1Leaf06
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := [131#u8,12#u8,229#u8,89#u8,101#u8,229#u8,161#u8,46#u8,6#u8,254#u8,136#u8,30#u8,186#u8,85#u8,70#u8,113#u8,39#u8,239#u8,200#u8,22#u8,165#u8,143#u8,19#u8,86#u8,221#u8,52#u8,155#u8,8#u8,206#u8,155#u8,204#u8,3#u8]
def n0 : List Nat := [131,12,229,89,101,229,161,46,6,254,136,30,186,85,70,113,39,239,200,22,165,143,19,86,221,52,155,8,206,155,204,3]
theorem cast0 : (c0.map decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
theorem select0 : ((JFo_Opening.value ⟨6,by decide⟩).val.drop 480).take 32=c0 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 480 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select0
def c1 : List U8 := [167#u8,249#u8,4#u8,2#u8,173#u8,116#u8,152#u8,15#u8,216#u8,225#u8,106#u8,34#u8,255#u8,246#u8,44#u8,95#u8,171#u8,192#u8,85#u8,127#u8,185#u8,225#u8,99#u8,33#u8,109#u8,187#u8,195#u8,116#u8,157#u8,78#u8,111#u8,99#u8]
def n1 : List Nat := [167,249,4,2,173,116,152,15,216,225,106,34,255,246,44,95,171,192,85,127,185,225,99,33,109,187,195,116,157,78,111,99]
theorem cast1 : (c1.map decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
theorem select1 : ((JFo_Opening.value ⟨6,by decide⟩).val.drop 512).take 32=c1 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 512 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select1
def c2 : List U8 := [56#u8,60#u8,78#u8,123#u8,146#u8,20#u8,94#u8,62#u8,118#u8,93#u8,144#u8,58#u8,222#u8,197#u8,182#u8,83#u8,16#u8,226#u8,119#u8,102#u8,176#u8,97#u8,131#u8,63#u8,119#u8,17#u8,155#u8,14#u8,14#u8,24#u8,89#u8,115#u8]
def n2 : List Nat := [56,60,78,123,146,20,94,62,118,93,144,58,222,197,182,83,16,226,119,102,176,97,131,63,119,17,155,14,14,24,89,115]
theorem cast2 : (c2.map decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
theorem select2 : ((JFo_Opening.value ⟨6,by decide⟩).val.drop 544).take 32=c2 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 544 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select2
def c3 : List U8 := [13#u8,180#u8,189#u8,2#u8,116#u8,128#u8,202#u8,19#u8,143#u8,191#u8,31#u8,90#u8,198#u8,232#u8,77#u8,12#u8,87#u8,108#u8,24#u8,87#u8,234#u8,162#u8,41#u8,54#u8,240#u8,115#u8,204#u8,2#u8,76#u8,194#u8,26#u8,75#u8]
def n3 : List Nat := [13,180,189,2,116,128,202,19,143,191,31,90,198,232,77,12,87,108,24,87,234,162,41,54,240,115,204,2,76,194,26,75]
theorem cast3 : (c3.map decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
theorem select3 : ((JFo_Opening.value ⟨6,by decide⟩).val.drop 576).take 32=c3 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 576 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select3
def c4 : List U8 := [0#u8,70#u8,150#u8,202#u8,116#u8,250#u8,117#u8,31#u8,91#u8,83#u8,65#u8,115#u8,172#u8,242#u8,215#u8,47#u8,82#u8,163#u8,49#u8,248#u8,147#u8,133#u8,146#u8,50#u8,32#u8,167#u8,29#u8,235#u8,190#u8,119#u8,75#u8,58#u8]
def n4 : List Nat := [0,70,150,202,116,250,117,31,91,83,65,115,172,242,215,47,82,163,49,248,147,133,146,50,32,167,29,235,190,119,75,58]
theorem cast4 : (c4.map decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem select4 : ((JFo_Opening.value ⟨6,by decide⟩).val.drop 640).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 640 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select4
theorem values : ((JFo_Opening.value ⟨6,by decide⟩).val.drop 480).take 128=c0++c1++c2++c3 := by
  have split : ((JFo_Opening.value ⟨6,by decide⟩).val.drop 480).take 128=(((JFo_Opening.value ⟨6,by decide⟩).val.drop 480).drop 0).take 32++(((JFo_Opening.value ⟨6,by decide⟩).val.drop 480).drop 32).take 32++(((JFo_Opening.value ⟨6,by decide⟩).val.drop 480).drop 64).take 32++(((JFo_Opening.value ⟨6,by decide⟩).val.drop 480).drop 96).take 32 := by
    rw [List.take_add (i:=32) (j:=96),List.take_add (i:=32) (j:=64),List.take_add (i:=32) (j:=32)]
    simp only [List.drop_drop,Nat.reduceAdd,List.append_assoc,List.drop_zero]
  simpa only [List.drop_drop,Nat.reduceAdd,select0,select1,select2,select3] using split
#print axioms values
def numeric : List Nat := [16,241]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JHe_C_Gr_M1.Hash006.message := by
  have step0 : [16,241]++n0++n1=JHe_C_Gr_M1.Hash006.B00.input++n1.drop 30 := by rfl
  have h0 : numeric=JHe_C_Gr_M1.Hash006.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have step1 : n1.drop 30++n2++n3=JHe_C_Gr_M1.Hash006.B01.input++n3.drop 30 := by rfl
  have h1 : rest1=JHe_C_Gr_M1.Hash006.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  have tail : rest2=JHe_C_Gr_M1.Hash006.tail := by rfl
  rw [h0,h1,tail]
  simp only [JHe_C_Gr_M1.Hash006.message,JHe_C_Gr_M1.Hash006.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem address : (flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨6,by decide⟩))).map Fin.val=JHe_C_Gr_M1.Hash006.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬1#usize=0#usize),if_pos (by rfl : 1#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨6,by decide⟩) 480#usize 608#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨6,by decide⟩) 640#usize 672#usize).val=c4 := select4
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have htag : (241#u8).val=241 := by scalar_tac
  simpa only [numeric,List.append_assoc,decodeByte,h16,htag] using regroup
#print axioms address
theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 1#usize (JFo_Opening.value ⟨6,by decide⟩)=ok (encodeState JHh_C_Gr_M1Roots.value006) := by
  rw [show Port4B_LeafCode.native _ hash 1#usize (JFo_Opening.value ⟨6,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨6,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨6,by decide⟩)))))=_
  have same : flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨6,by decide⟩))=JHh_C_Gr_M1Roots.input006 :=
    (List.map_inj_right (fun _ _ h => Fin.val_injective h)).mp (address.trans JHh_LeafNumerics1.numeric006.symm)
  rw [same,JHh_C_Gr_M1Roots.hash006]
#print axioms source
end AspisR1.JHh_C_Gu_M1Leaf06
end
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_M1Leaf07
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := [199#u8,205#u8,132#u8,63#u8,65#u8,20#u8,42#u8,102#u8,58#u8,238#u8,118#u8,9#u8,191#u8,87#u8,215#u8,81#u8,146#u8,121#u8,193#u8,106#u8,130#u8,7#u8,58#u8,63#u8,173#u8,166#u8,44#u8,127#u8,109#u8,11#u8,201#u8,59#u8]
def n0 : List Nat := [199,205,132,63,65,20,42,102,58,238,118,9,191,87,215,81,146,121,193,106,130,7,58,63,173,166,44,127,109,11,201,59]
theorem cast0 : (c0.map decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
theorem select0 : ((JFo_Opening.value ⟨7,by decide⟩).val.drop 480).take 32=c0 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 480 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select0
def c1 : List U8 := [255#u8,66#u8,210#u8,56#u8,83#u8,108#u8,227#u8,124#u8,182#u8,41#u8,45#u8,16#u8,253#u8,42#u8,101#u8,65#u8,77#u8,92#u8,54#u8,97#u8,173#u8,243#u8,241#u8,77#u8,148#u8,26#u8,176#u8,116#u8,17#u8,120#u8,247#u8,51#u8]
def n1 : List Nat := [255,66,210,56,83,108,227,124,182,41,45,16,253,42,101,65,77,92,54,97,173,243,241,77,148,26,176,116,17,120,247,51]
theorem cast1 : (c1.map decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
theorem select1 : ((JFo_Opening.value ⟨7,by decide⟩).val.drop 512).take 32=c1 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 512 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select1
def c2 : List U8 := [238#u8,3#u8,54#u8,78#u8,105#u8,139#u8,110#u8,126#u8,116#u8,7#u8,61#u8,103#u8,99#u8,253#u8,123#u8,32#u8,88#u8,79#u8,16#u8,75#u8,84#u8,32#u8,129#u8,53#u8,254#u8,218#u8,212#u8,4#u8,13#u8,226#u8,4#u8,84#u8]
def n2 : List Nat := [238,3,54,78,105,139,110,126,116,7,61,103,99,253,123,32,88,79,16,75,84,32,129,53,254,218,212,4,13,226,4,84]
theorem cast2 : (c2.map decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
theorem select2 : ((JFo_Opening.value ⟨7,by decide⟩).val.drop 544).take 32=c2 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 544 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select2
def c3 : List U8 := [97#u8,5#u8,131#u8,58#u8,243#u8,193#u8,202#u8,90#u8,155#u8,126#u8,232#u8,73#u8,205#u8,103#u8,239#u8,63#u8,219#u8,255#u8,28#u8,63#u8,175#u8,137#u8,115#u8,110#u8,53#u8,95#u8,191#u8,46#u8,216#u8,191#u8,93#u8,57#u8]
def n3 : List Nat := [97,5,131,58,243,193,202,90,155,126,232,73,205,103,239,63,219,255,28,63,175,137,115,110,53,95,191,46,216,191,93,57]
theorem cast3 : (c3.map decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
theorem select3 : ((JFo_Opening.value ⟨7,by decide⟩).val.drop 576).take 32=c3 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 576 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select3
def c4 : List U8 := [160#u8,70#u8,163#u8,147#u8,66#u8,138#u8,34#u8,228#u8,239#u8,224#u8,7#u8,198#u8,220#u8,173#u8,53#u8,0#u8,199#u8,83#u8,250#u8,95#u8,173#u8,174#u8,108#u8,49#u8,245#u8,88#u8,187#u8,112#u8,90#u8,15#u8,199#u8,49#u8]
def n4 : List Nat := [160,70,163,147,66,138,34,228,239,224,7,198,220,173,53,0,199,83,250,95,173,174,108,49,245,88,187,112,90,15,199,49]
theorem cast4 : (c4.map decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem select4 : ((JFo_Opening.value ⟨7,by decide⟩).val.drop 640).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 640 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select4
theorem values : ((JFo_Opening.value ⟨7,by decide⟩).val.drop 480).take 128=c0++c1++c2++c3 := by
  have split : ((JFo_Opening.value ⟨7,by decide⟩).val.drop 480).take 128=(((JFo_Opening.value ⟨7,by decide⟩).val.drop 480).drop 0).take 32++(((JFo_Opening.value ⟨7,by decide⟩).val.drop 480).drop 32).take 32++(((JFo_Opening.value ⟨7,by decide⟩).val.drop 480).drop 64).take 32++(((JFo_Opening.value ⟨7,by decide⟩).val.drop 480).drop 96).take 32 := by
    rw [List.take_add (i:=32) (j:=96),List.take_add (i:=32) (j:=64),List.take_add (i:=32) (j:=32)]
    simp only [List.drop_drop,Nat.reduceAdd,List.append_assoc,List.drop_zero]
  simpa only [List.drop_drop,Nat.reduceAdd,select0,select1,select2,select3] using split
#print axioms values
def numeric : List Nat := [16,241]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JHe_C_Gr_M1.Hash007.message := by
  have step0 : [16,241]++n0++n1=JHe_C_Gr_M1.Hash007.B00.input++n1.drop 30 := by rfl
  have h0 : numeric=JHe_C_Gr_M1.Hash007.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have step1 : n1.drop 30++n2++n3=JHe_C_Gr_M1.Hash007.B01.input++n3.drop 30 := by rfl
  have h1 : rest1=JHe_C_Gr_M1.Hash007.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  have tail : rest2=JHe_C_Gr_M1.Hash007.tail := by rfl
  rw [h0,h1,tail]
  simp only [JHe_C_Gr_M1.Hash007.message,JHe_C_Gr_M1.Hash007.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem address : (flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨7,by decide⟩))).map Fin.val=JHe_C_Gr_M1.Hash007.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬1#usize=0#usize),if_pos (by rfl : 1#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨7,by decide⟩) 480#usize 608#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨7,by decide⟩) 640#usize 672#usize).val=c4 := select4
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have htag : (241#u8).val=241 := by scalar_tac
  simpa only [numeric,List.append_assoc,decodeByte,h16,htag] using regroup
#print axioms address
theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 1#usize (JFo_Opening.value ⟨7,by decide⟩)=ok (encodeState JHh_C_Gr_M1Roots.value007) := by
  rw [show Port4B_LeafCode.native _ hash 1#usize (JFo_Opening.value ⟨7,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨7,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨7,by decide⟩)))))=_
  have same : flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨7,by decide⟩))=JHh_C_Gr_M1Roots.input007 :=
    (List.map_inj_right (fun _ _ h => Fin.val_injective h)).mp (address.trans JHh_LeafNumerics1.numeric007.symm)
  rw [same,JHh_C_Gr_M1Roots.hash007]
#print axioms source
end AspisR1.JHh_C_Gu_M1Leaf07
end
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_M1Leaf08
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := [31#u8,228#u8,60#u8,14#u8,188#u8,4#u8,1#u8,16#u8,3#u8,51#u8,205#u8,61#u8,22#u8,216#u8,127#u8,64#u8,111#u8,39#u8,56#u8,100#u8,151#u8,162#u8,168#u8,12#u8,108#u8,4#u8,56#u8,55#u8,52#u8,139#u8,116#u8,8#u8]
def n0 : List Nat := [31,228,60,14,188,4,1,16,3,51,205,61,22,216,127,64,111,39,56,100,151,162,168,12,108,4,56,55,52,139,116,8]
theorem cast0 : (c0.map decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
theorem select0 : ((JFo_Opening.value ⟨8,by decide⟩).val.drop 480).take 32=c0 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 480 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select0
def c1 : List U8 := [195#u8,41#u8,104#u8,37#u8,205#u8,137#u8,110#u8,91#u8,158#u8,49#u8,120#u8,81#u8,231#u8,153#u8,189#u8,107#u8,3#u8,127#u8,152#u8,86#u8,253#u8,116#u8,239#u8,41#u8,97#u8,14#u8,51#u8,10#u8,70#u8,128#u8,63#u8,86#u8]
def n1 : List Nat := [195,41,104,37,205,137,110,91,158,49,120,81,231,153,189,107,3,127,152,86,253,116,239,41,97,14,51,10,70,128,63,86]
theorem cast1 : (c1.map decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
theorem select1 : ((JFo_Opening.value ⟨8,by decide⟩).val.drop 512).take 32=c1 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 512 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select1
def c2 : List U8 := [151#u8,203#u8,205#u8,61#u8,226#u8,122#u8,240#u8,47#u8,102#u8,76#u8,100#u8,106#u8,232#u8,96#u8,182#u8,11#u8,144#u8,149#u8,103#u8,60#u8,5#u8,16#u8,151#u8,7#u8,110#u8,75#u8,94#u8,22#u8,159#u8,148#u8,68#u8,45#u8]
def n2 : List Nat := [151,203,205,61,226,122,240,47,102,76,100,106,232,96,182,11,144,149,103,60,5,16,151,7,110,75,94,22,159,148,68,45]
theorem cast2 : (c2.map decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
theorem select2 : ((JFo_Opening.value ⟨8,by decide⟩).val.drop 544).take 32=c2 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 544 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select2
def c3 : List U8 := [136#u8,148#u8,106#u8,28#u8,96#u8,0#u8,37#u8,71#u8,62#u8,3#u8,249#u8,75#u8,86#u8,158#u8,36#u8,52#u8,167#u8,209#u8,200#u8,53#u8,86#u8,100#u8,16#u8,26#u8,111#u8,139#u8,209#u8,92#u8,65#u8,99#u8,199#u8,102#u8]
def n3 : List Nat := [136,148,106,28,96,0,37,71,62,3,249,75,86,158,36,52,167,209,200,53,86,100,16,26,111,139,209,92,65,99,199,102]
theorem cast3 : (c3.map decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
theorem select3 : ((JFo_Opening.value ⟨8,by decide⟩).val.drop 576).take 32=c3 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 576 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select3
def c4 : List U8 := [101#u8,151#u8,25#u8,181#u8,156#u8,92#u8,90#u8,128#u8,29#u8,81#u8,60#u8,176#u8,11#u8,166#u8,113#u8,166#u8,202#u8,229#u8,44#u8,204#u8,2#u8,30#u8,235#u8,22#u8,210#u8,85#u8,202#u8,29#u8,149#u8,27#u8,159#u8,8#u8]
def n4 : List Nat := [101,151,25,181,156,92,90,128,29,81,60,176,11,166,113,166,202,229,44,204,2,30,235,22,210,85,202,29,149,27,159,8]
theorem cast4 : (c4.map decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem select4 : ((JFo_Opening.value ⟨8,by decide⟩).val.drop 640).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 640 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select4
theorem values : ((JFo_Opening.value ⟨8,by decide⟩).val.drop 480).take 128=c0++c1++c2++c3 := by
  have split : ((JFo_Opening.value ⟨8,by decide⟩).val.drop 480).take 128=(((JFo_Opening.value ⟨8,by decide⟩).val.drop 480).drop 0).take 32++(((JFo_Opening.value ⟨8,by decide⟩).val.drop 480).drop 32).take 32++(((JFo_Opening.value ⟨8,by decide⟩).val.drop 480).drop 64).take 32++(((JFo_Opening.value ⟨8,by decide⟩).val.drop 480).drop 96).take 32 := by
    rw [List.take_add (i:=32) (j:=96),List.take_add (i:=32) (j:=64),List.take_add (i:=32) (j:=32)]
    simp only [List.drop_drop,Nat.reduceAdd,List.append_assoc,List.drop_zero]
  simpa only [List.drop_drop,Nat.reduceAdd,select0,select1,select2,select3] using split
#print axioms values
def numeric : List Nat := [16,241]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JHe_C_Gr_M1.Hash008.message := by
  have step0 : [16,241]++n0++n1=JHe_C_Gr_M1.Hash008.B00.input++n1.drop 30 := by rfl
  have h0 : numeric=JHe_C_Gr_M1.Hash008.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have step1 : n1.drop 30++n2++n3=JHe_C_Gr_M1.Hash008.B01.input++n3.drop 30 := by rfl
  have h1 : rest1=JHe_C_Gr_M1.Hash008.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  have tail : rest2=JHe_C_Gr_M1.Hash008.tail := by rfl
  rw [h0,h1,tail]
  simp only [JHe_C_Gr_M1.Hash008.message,JHe_C_Gr_M1.Hash008.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem address : (flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨8,by decide⟩))).map Fin.val=JHe_C_Gr_M1.Hash008.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬1#usize=0#usize),if_pos (by rfl : 1#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨8,by decide⟩) 480#usize 608#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨8,by decide⟩) 640#usize 672#usize).val=c4 := select4
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have htag : (241#u8).val=241 := by scalar_tac
  simpa only [numeric,List.append_assoc,decodeByte,h16,htag] using regroup
#print axioms address
theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 1#usize (JFo_Opening.value ⟨8,by decide⟩)=ok (encodeState JHh_C_Gr_M1Roots.value008) := by
  rw [show Port4B_LeafCode.native _ hash 1#usize (JFo_Opening.value ⟨8,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨8,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨8,by decide⟩)))))=_
  have same : flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨8,by decide⟩))=JHh_C_Gr_M1Roots.input008 :=
    (List.map_inj_right (fun _ _ h => Fin.val_injective h)).mp (address.trans JHh_LeafNumerics1.numeric008.symm)
  rw [same,JHh_C_Gr_M1Roots.hash008]
#print axioms source
end AspisR1.JHh_C_Gu_M1Leaf08
end
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_M1Leaf09
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := [4#u8,120#u8,174#u8,62#u8,238#u8,149#u8,121#u8,29#u8,97#u8,151#u8,132#u8,28#u8,255#u8,24#u8,21#u8,77#u8,6#u8,9#u8,251#u8,123#u8,41#u8,87#u8,217#u8,20#u8,227#u8,129#u8,60#u8,36#u8,47#u8,212#u8,160#u8,70#u8]
def n0 : List Nat := [4,120,174,62,238,149,121,29,97,151,132,28,255,24,21,77,6,9,251,123,41,87,217,20,227,129,60,36,47,212,160,70]
theorem cast0 : (c0.map decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
theorem select0 : ((JFo_Opening.value ⟨9,by decide⟩).val.drop 480).take 32=c0 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 480 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select0
def c1 : List U8 := [137#u8,88#u8,115#u8,113#u8,236#u8,248#u8,222#u8,28#u8,253#u8,152#u8,165#u8,26#u8,27#u8,209#u8,14#u8,66#u8,77#u8,186#u8,222#u8,10#u8,175#u8,152#u8,0#u8,61#u8,173#u8,196#u8,214#u8,59#u8,48#u8,238#u8,96#u8,70#u8]
def n1 : List Nat := [137,88,115,113,236,248,222,28,253,152,165,26,27,209,14,66,77,186,222,10,175,152,0,61,173,196,214,59,48,238,96,70]
theorem cast1 : (c1.map decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
theorem select1 : ((JFo_Opening.value ⟨9,by decide⟩).val.drop 512).take 32=c1 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 512 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select1
def c2 : List U8 := [40#u8,22#u8,152#u8,32#u8,163#u8,90#u8,230#u8,105#u8,82#u8,122#u8,177#u8,118#u8,223#u8,13#u8,100#u8,48#u8,53#u8,149#u8,61#u8,32#u8,29#u8,232#u8,214#u8,71#u8,144#u8,39#u8,9#u8,74#u8,52#u8,150#u8,134#u8,46#u8]
def n2 : List Nat := [40,22,152,32,163,90,230,105,82,122,177,118,223,13,100,48,53,149,61,32,29,232,214,71,144,39,9,74,52,150,134,46]
theorem cast2 : (c2.map decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
theorem select2 : ((JFo_Opening.value ⟨9,by decide⟩).val.drop 544).take 32=c2 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 544 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select2
def c3 : List U8 := [177#u8,47#u8,3#u8,75#u8,95#u8,4#u8,15#u8,67#u8,250#u8,117#u8,206#u8,64#u8,182#u8,198#u8,102#u8,95#u8,71#u8,254#u8,40#u8,106#u8,24#u8,250#u8,53#u8,25#u8,133#u8,62#u8,26#u8,105#u8,202#u8,124#u8,219#u8,65#u8]
def n3 : List Nat := [177,47,3,75,95,4,15,67,250,117,206,64,182,198,102,95,71,254,40,106,24,250,53,25,133,62,26,105,202,124,219,65]
theorem cast3 : (c3.map decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
theorem select3 : ((JFo_Opening.value ⟨9,by decide⟩).val.drop 576).take 32=c3 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 576 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select3
def c4 : List U8 := [205#u8,159#u8,239#u8,43#u8,111#u8,8#u8,14#u8,143#u8,101#u8,114#u8,220#u8,111#u8,61#u8,148#u8,73#u8,175#u8,217#u8,89#u8,127#u8,84#u8,245#u8,173#u8,28#u8,177#u8,12#u8,59#u8,202#u8,129#u8,3#u8,121#u8,250#u8,187#u8]
def n4 : List Nat := [205,159,239,43,111,8,14,143,101,114,220,111,61,148,73,175,217,89,127,84,245,173,28,177,12,59,202,129,3,121,250,187]
theorem cast4 : (c4.map decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem select4 : ((JFo_Opening.value ⟨9,by decide⟩).val.drop 640).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 640 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms select4
theorem values : ((JFo_Opening.value ⟨9,by decide⟩).val.drop 480).take 128=c0++c1++c2++c3 := by
  have split : ((JFo_Opening.value ⟨9,by decide⟩).val.drop 480).take 128=(((JFo_Opening.value ⟨9,by decide⟩).val.drop 480).drop 0).take 32++(((JFo_Opening.value ⟨9,by decide⟩).val.drop 480).drop 32).take 32++(((JFo_Opening.value ⟨9,by decide⟩).val.drop 480).drop 64).take 32++(((JFo_Opening.value ⟨9,by decide⟩).val.drop 480).drop 96).take 32 := by
    rw [List.take_add (i:=32) (j:=96),List.take_add (i:=32) (j:=64),List.take_add (i:=32) (j:=32)]
    simp only [List.drop_drop,Nat.reduceAdd,List.append_assoc,List.drop_zero]
  simpa only [List.drop_drop,Nat.reduceAdd,select0,select1,select2,select3] using split
#print axioms values
def numeric : List Nat := [16,241]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JHe_C_Gr_M1.Hash009.message := by
  have step0 : [16,241]++n0++n1=JHe_C_Gr_M1.Hash009.B00.input++n1.drop 30 := by rfl
  have h0 : numeric=JHe_C_Gr_M1.Hash009.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have step1 : n1.drop 30++n2++n3=JHe_C_Gr_M1.Hash009.B01.input++n3.drop 30 := by rfl
  have h1 : rest1=JHe_C_Gr_M1.Hash009.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  have tail : rest2=JHe_C_Gr_M1.Hash009.tail := by rfl
  rw [h0,h1,tail]
  simp only [JHe_C_Gr_M1.Hash009.message,JHe_C_Gr_M1.Hash009.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem address : (flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨9,by decide⟩))).map Fin.val=JHe_C_Gr_M1.Hash009.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬1#usize=0#usize),if_pos (by rfl : 1#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨9,by decide⟩) 480#usize 608#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨9,by decide⟩) 640#usize 672#usize).val=c4 := select4
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have htag : (241#u8).val=241 := by scalar_tac
  simpa only [numeric,List.append_assoc,decodeByte,h16,htag] using regroup
#print axioms address
theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 1#usize (JFo_Opening.value ⟨9,by decide⟩)=ok (encodeState JHh_C_Gr_M1Roots.value009) := by
  rw [show Port4B_LeafCode.native _ hash 1#usize (JFo_Opening.value ⟨9,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨9,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨9,by decide⟩)))))=_
  have same : flatten (Port4B_LeafCode.input 1#usize (JFo_Opening.value ⟨9,by decide⟩))=JHh_C_Gr_M1Roots.input009 :=
    (List.map_inj_right (fun _ _ h => Fin.val_injective h)).mp (address.trans JHh_LeafNumerics1.numeric009.symm)
  rw [same,JHh_C_Gr_M1Roots.hash009]
#print axioms source
end AspisR1.JHh_C_Gu_M1Leaf09
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gu_LeafIteration1
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
def opening (i : Fin 10) : Slice U8 := JFo_Opening.value ⟨i.val,by have := i.isLt;omega⟩
def value (i : Fin 10) : AspisV8R19.SourceDuplexStep.State := match i.val with
  | 0 => JHh_C_Gr_M1Roots.value000
  | 1 => JHh_C_Gr_M1Roots.value001
  | 2 => JHh_C_Gr_M1Roots.value002
  | 3 => JHh_C_Gr_M1Roots.value003
  | 4 => JHh_C_Gr_M1Roots.value004
  | 5 => JHh_C_Gr_M1Roots.value005
  | 6 => JHh_C_Gr_M1Roots.value006
  | 7 => JHh_C_Gr_M1Roots.value007
  | 8 => JHh_C_Gr_M1Roots.value008
  | _ => JHh_C_Gr_M1Roots.value009
theorem leaf {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) (i : Fin 10) :
    Port4B_LeafCode.native (JGy_G_JGc_TX2_RealLeaves.dictionary D) hash 1#usize (opening i)=ok (encodeState (value i)) := by
  fin_cases i
  · exact JHh_C_Gu_M1Leaf00.source D hash
  · exact JHh_C_Gu_M1Leaf01.source D hash
  · exact JHh_C_Gu_M1Leaf02.source D hash
  · exact JHh_C_Gu_M1Leaf03.source D hash
  · exact JHh_C_Gu_M1Leaf04.source D hash
  · exact JHh_C_Gu_M1Leaf05.source D hash
  · exact JHh_C_Gu_M1Leaf06.source D hash
  · exact JHh_C_Gu_M1Leaf07.source D hash
  · exact JHh_C_Gu_M1Leaf08.source D hash
  · exact JHh_C_Gu_M1Leaf09.source D hash
#print axioms leaf
theorem opening_read (i : Fin 10) :
    Port4B_Opening.opening JFx_NativeBytes.proof (Port4B_NativeLeaf.openingIndex 0#usize
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 1 i.val))=ok (opening i) := by
  have member : i.val ∈ OraclePortSelectedDraft.batchPositions 0 := List.mem_range.mpr i.isLt
  have decoded := (Port4B_KeyDecode.packed JGr_Keys.q 0 1 i.val member 0#usize rfl).2
  have cursor : Port4B_NativeLeaf.openingIndex 0#usize (MultiproofConeSortOrder.packed JGr_Keys.q 0 1 i.val)=UScalar.ofNat i.val (by have := i.isLt;scalar_tac) := UScalar.eq_of_val_eq decoded
  have read := JFo_Opening.call (⟨i.val,by have := i.isLt;omega⟩ : Fin 22)
  have same : JFo_Opening.cursor (⟨i.val,by have := i.isLt;omega⟩ : Fin 22)=UScalar.ofNat i.val (by have := i.isLt;scalar_tac) := rfl
  rw [same] at read
  rw [cursor]
  exact read
#print axioms opening_read
theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (i : Fin 10) (pos : Usize) (keys : Array U64 16#usize) (root : Array U8 32#usize)
    (s : reference.Scratch) (more : pos<10#usize) (room : s.n.val<16)
    (keyRead : Array.index_usize keys pos=ok (MultiproofConeSortOrder.packed JGr_Keys.q 0 1 i.val)) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 0#usize 10#usize 1#usize keys s.idx s.val s.n pos=
        (do let out ← reference.leaf_step s
              (Port4B_NativeLeaf.decodedIndex (MultiproofConeSortOrder.packed JGr_Keys.q 0 1 i.val))
              (encodeState (value i))
            ok (Port4B_LeafStep.project s (Usize.wrapping_add pos 1#usize) out)) := by
  apply Port4B_NativeLeaf.step Port4B_Install.leaves (JGy_G_JGc_TX2_RealLeaves.dictionary D) hash
    JFx_NativeBytes.proof root 1#usize 0#usize 10#usize 1#usize pos keys s
    _ (opening i) _ more room keyRead
  · exact opening_read i
  · exact leaf D hash i
#print axioms source
end AspisR1.JHh_C_Gu_LeafIteration1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gu_Scratch1
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGu_Keys.keys

def s00 (s : reference.Scratch) : reference.Scratch := {s with n:=0#usize,«at»:=0#usize}
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s00 s) 65593#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩)) (by change (0:Nat)<16; decide)

theorem body00 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 0#usize 10#usize 1#usize (JGu_Keys.keys 1)
      (s00 s).idx (s00 s).val (s00 s).n 0#usize=
        ok (.cont ((s01 s).idx,(s01 s).val,(s01 s).n,1#usize)) := by
  have read := JGu_Keys.stream1 0#usize 0 (by decide) rfl
  have native := JHh_C_Gu_LeafIteration1.source D hash ⟨6,by decide⟩
    0#usize (JGu_Keys.keys 1) root (s00 s) (by decide) (by change (0:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 6 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 1 6)=65593#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 1 6 member 0#usize rfl).1
  have fresh : ¬(0<(s00 s).n.val ∧ (s00 s).idx.val[(s00 s).n.val-1]! = 65593#u32) := by
    intro h
    exact (Nat.lt_irrefl 0) h.1
  rw [decoded,JGk_TX2_LeafPush.step (s00 s) 65593#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩)) (by change (0:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 0#usize 1#usize=1#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 0#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s01] using native
#print axioms body00
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s01 s) 93499#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨0,by decide⟩)) (by change (1:Nat)<16; decide)

theorem body01 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 0#usize 10#usize 1#usize (JGu_Keys.keys 1)
      (s01 s).idx (s01 s).val (s01 s).n 1#usize=
        ok (.cont ((s02 s).idx,(s02 s).val,(s02 s).n,2#usize)) := by
  have read := JGu_Keys.stream1 1#usize 1 (by decide) rfl
  have native := JHh_C_Gu_LeafIteration1.source D hash ⟨0,by decide⟩
    1#usize (JGu_Keys.keys 1) root (s01 s) (by decide) (by change (1:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 0 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 1 0)=93499#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 1 0 member 0#usize rfl).1
  have fresh : ¬(0<(s01 s).n.val ∧ (s01 s).idx.val[(s01 s).n.val-1]! = 93499#u32) := by
    have last : (s01 s).idx.val[(s01 s).n.val-1]! = 65593#u32 :=
      JGk_TX2_LeafPush.last (s00 s) 65593#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩)) (by change (0:Nat)<16; decide)
    intro h
    exact (by decide : 65593#u32≠93499#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s01 s) 93499#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨0,by decide⟩)) (by change (1:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 1#usize 1#usize=2#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 1#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s02] using native
#print axioms body01
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s02 s) 147529#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨1,by decide⟩)) (by change (2:Nat)<16; decide)

theorem body02 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 0#usize 10#usize 1#usize (JGu_Keys.keys 1)
      (s02 s).idx (s02 s).val (s02 s).n 2#usize=
        ok (.cont ((s03 s).idx,(s03 s).val,(s03 s).n,3#usize)) := by
  have read := JGu_Keys.stream1 2#usize 2 (by decide) rfl
  have native := JHh_C_Gu_LeafIteration1.source D hash ⟨1,by decide⟩
    2#usize (JGu_Keys.keys 1) root (s02 s) (by decide) (by change (2:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 1 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 1 1)=147529#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 1 1 member 0#usize rfl).1
  have fresh : ¬(0<(s02 s).n.val ∧ (s02 s).idx.val[(s02 s).n.val-1]! = 147529#u32) := by
    have last : (s02 s).idx.val[(s02 s).n.val-1]! = 93499#u32 :=
      JGk_TX2_LeafPush.last (s01 s) 93499#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨0,by decide⟩)) (by change (1:Nat)<16; decide)
    intro h
    exact (by decide : 93499#u32≠147529#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s02 s) 147529#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨1,by decide⟩)) (by change (2:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 2#usize 1#usize=3#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 2#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s03] using native
#print axioms body02
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s03 s) 159813#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨9,by decide⟩)) (by change (3:Nat)<16; decide)

theorem body03 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 0#usize 10#usize 1#usize (JGu_Keys.keys 1)
      (s03 s).idx (s03 s).val (s03 s).n 3#usize=
        ok (.cont ((s04 s).idx,(s04 s).val,(s04 s).n,4#usize)) := by
  have read := JGu_Keys.stream1 3#usize 3 (by decide) rfl
  have native := JHh_C_Gu_LeafIteration1.source D hash ⟨9,by decide⟩
    3#usize (JGu_Keys.keys 1) root (s03 s) (by decide) (by change (3:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 9 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 1 9)=159813#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 1 9 member 0#usize rfl).1
  have fresh : ¬(0<(s03 s).n.val ∧ (s03 s).idx.val[(s03 s).n.val-1]! = 159813#u32) := by
    have last : (s03 s).idx.val[(s03 s).n.val-1]! = 147529#u32 :=
      JGk_TX2_LeafPush.last (s02 s) 147529#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨1,by decide⟩)) (by change (2:Nat)<16; decide)
    intro h
    exact (by decide : 147529#u32≠159813#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s03 s) 159813#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨9,by decide⟩)) (by change (3:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 3#usize 1#usize=4#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 3#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s04] using native
#print axioms body03
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s04 s) 183859#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨7,by decide⟩)) (by change (4:Nat)<16; decide)

theorem body04 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 0#usize 10#usize 1#usize (JGu_Keys.keys 1)
      (s04 s).idx (s04 s).val (s04 s).n 4#usize=
        ok (.cont ((s05 s).idx,(s05 s).val,(s05 s).n,5#usize)) := by
  have read := JGu_Keys.stream1 4#usize 4 (by decide) rfl
  have native := JHh_C_Gu_LeafIteration1.source D hash ⟨7,by decide⟩
    4#usize (JGu_Keys.keys 1) root (s04 s) (by decide) (by change (4:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 7 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 1 7)=183859#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 1 7 member 0#usize rfl).1
  have fresh : ¬(0<(s04 s).n.val ∧ (s04 s).idx.val[(s04 s).n.val-1]! = 183859#u32) := by
    have last : (s04 s).idx.val[(s04 s).n.val-1]! = 159813#u32 :=
      JGk_TX2_LeafPush.last (s03 s) 159813#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨9,by decide⟩)) (by change (3:Nat)<16; decide)
    intro h
    exact (by decide : 159813#u32≠183859#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s04 s) 183859#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨7,by decide⟩)) (by change (4:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 4#usize 1#usize=5#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 4#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s05] using native
#print axioms body04
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s05 s) 192317#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨5,by decide⟩)) (by change (5:Nat)<16; decide)

theorem body05 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 0#usize 10#usize 1#usize (JGu_Keys.keys 1)
      (s05 s).idx (s05 s).val (s05 s).n 5#usize=
        ok (.cont ((s06 s).idx,(s06 s).val,(s06 s).n,6#usize)) := by
  have read := JGu_Keys.stream1 5#usize 5 (by decide) rfl
  have native := JHh_C_Gu_LeafIteration1.source D hash ⟨5,by decide⟩
    5#usize (JGu_Keys.keys 1) root (s05 s) (by decide) (by change (5:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 5 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 1 5)=192317#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 1 5 member 0#usize rfl).1
  have fresh : ¬(0<(s05 s).n.val ∧ (s05 s).idx.val[(s05 s).n.val-1]! = 192317#u32) := by
    have last : (s05 s).idx.val[(s05 s).n.val-1]! = 183859#u32 :=
      JGk_TX2_LeafPush.last (s04 s) 183859#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨7,by decide⟩)) (by change (4:Nat)<16; decide)
    intro h
    exact (by decide : 183859#u32≠192317#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s05 s) 192317#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨5,by decide⟩)) (by change (5:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 5#usize 1#usize=6#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 5#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s06] using native
#print axioms body05
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s06 s) 193093#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨8,by decide⟩)) (by change (6:Nat)<16; decide)

theorem body06 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 0#usize 10#usize 1#usize (JGu_Keys.keys 1)
      (s06 s).idx (s06 s).val (s06 s).n 6#usize=
        ok (.cont ((s07 s).idx,(s07 s).val,(s07 s).n,7#usize)) := by
  have read := JGu_Keys.stream1 6#usize 6 (by decide) rfl
  have native := JHh_C_Gu_LeafIteration1.source D hash ⟨8,by decide⟩
    6#usize (JGu_Keys.keys 1) root (s06 s) (by decide) (by change (6:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 8 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 1 8)=193093#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 1 8 member 0#usize rfl).1
  have fresh : ¬(0<(s06 s).n.val ∧ (s06 s).idx.val[(s06 s).n.val-1]! = 193093#u32) := by
    have last : (s06 s).idx.val[(s06 s).n.val-1]! = 192317#u32 :=
      JGk_TX2_LeafPush.last (s05 s) 192317#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨5,by decide⟩)) (by change (5:Nat)<16; decide)
    intro h
    exact (by decide : 192317#u32≠193093#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s06 s) 193093#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨8,by decide⟩)) (by change (6:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 6#usize 1#usize=7#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 6#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s07] using native
#print axioms body06
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s07 s) 209371#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨4,by decide⟩)) (by change (7:Nat)<16; decide)

theorem body07 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 0#usize 10#usize 1#usize (JGu_Keys.keys 1)
      (s07 s).idx (s07 s).val (s07 s).n 7#usize=
        ok (.cont ((s08 s).idx,(s08 s).val,(s08 s).n,8#usize)) := by
  have read := JGu_Keys.stream1 7#usize 7 (by decide) rfl
  have native := JHh_C_Gu_LeafIteration1.source D hash ⟨4,by decide⟩
    7#usize (JGu_Keys.keys 1) root (s07 s) (by decide) (by change (7:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 4 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 1 4)=209371#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 1 4 member 0#usize rfl).1
  have fresh : ¬(0<(s07 s).n.val ∧ (s07 s).idx.val[(s07 s).n.val-1]! = 209371#u32) := by
    have last : (s07 s).idx.val[(s07 s).n.val-1]! = 193093#u32 :=
      JGk_TX2_LeafPush.last (s06 s) 193093#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨8,by decide⟩)) (by change (6:Nat)<16; decide)
    intro h
    exact (by decide : 193093#u32≠209371#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s07 s) 209371#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨4,by decide⟩)) (by change (7:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 7#usize 1#usize=8#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 7#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s08] using native
#print axioms body07
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s08 s) 216823#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨2,by decide⟩)) (by change (8:Nat)<16; decide)

theorem body08 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 0#usize 10#usize 1#usize (JGu_Keys.keys 1)
      (s08 s).idx (s08 s).val (s08 s).n 8#usize=
        ok (.cont ((s09 s).idx,(s09 s).val,(s09 s).n,9#usize)) := by
  have read := JGu_Keys.stream1 8#usize 8 (by decide) rfl
  have native := JHh_C_Gu_LeafIteration1.source D hash ⟨2,by decide⟩
    8#usize (JGu_Keys.keys 1) root (s08 s) (by decide) (by change (8:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 2 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 1 2)=216823#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 1 2 member 0#usize rfl).1
  have fresh : ¬(0<(s08 s).n.val ∧ (s08 s).idx.val[(s08 s).n.val-1]! = 216823#u32) := by
    have last : (s08 s).idx.val[(s08 s).n.val-1]! = 209371#u32 :=
      JGk_TX2_LeafPush.last (s07 s) 209371#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨4,by decide⟩)) (by change (7:Nat)<16; decide)
    intro h
    exact (by decide : 209371#u32≠216823#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s08 s) 216823#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨2,by decide⟩)) (by change (8:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 8#usize 1#usize=9#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 8#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s09] using native
#print axioms body08
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push (s09 s) 245899#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨3,by decide⟩)) (by change (9:Nat)<16; decide)

theorem body09 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 0#usize 10#usize 1#usize (JGu_Keys.keys 1)
      (s09 s).idx (s09 s).val (s09 s).n 9#usize=
        ok (.cont ((s10 s).idx,(s10 s).val,(s10 s).n,10#usize)) := by
  have read := JGu_Keys.stream1 9#usize 9 (by decide) rfl
  have native := JHh_C_Gu_LeafIteration1.source D hash ⟨3,by decide⟩
    9#usize (JGu_Keys.keys 1) root (s09 s) (by decide) (by change (9:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : 3 ∈ OraclePortSelectedDraft.batchPositions 0 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 1 3)=245899#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGr_Keys.q 0 1 3 member 0#usize rfl).1
  have fresh : ¬(0<(s09 s).n.val ∧ (s09 s).idx.val[(s09 s).n.val-1]! = 245899#u32) := by
    have last : (s09 s).idx.val[(s09 s).n.val-1]! = 216823#u32 :=
      JGk_TX2_LeafPush.last (s08 s) 216823#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨2,by decide⟩)) (by change (8:Nat)<16; decide)
    intro h
    exact (by decide : 216823#u32≠245899#u32) (last.symm.trans h.2)
  rw [decoded,JGk_TX2_LeafPush.step (s09 s) 245899#u32 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨3,by decide⟩)) (by change (9:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add 9#usize 1#usize=10#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 9#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s10] using native
#print axioms body09
theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize (s00 s).idx (s00 s).val hash 0#usize 10#usize 1#usize
      (JGu_Keys.keys 1) (s00 s).n 0#usize=
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize (s10 s).idx (s10 s).val hash 0#usize 10#usize 1#usize
      (JGu_Keys.keys 1) (s10 s).n 10#usize := by
  exact (JGu_Keys.advance_loop (JGy_G_JGc_TX2_RealLeaves.dictionary D) hash root 1#usize 1#usize 0#usize 1#usize (s00 s) (s01 s) (body00 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGy_G_JGc_TX2_RealLeaves.dictionary D) hash root 1#usize 1#usize 1#usize 2#usize (s01 s) (s02 s) (body01 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGy_G_JGc_TX2_RealLeaves.dictionary D) hash root 1#usize 1#usize 2#usize 3#usize (s02 s) (s03 s) (body02 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGy_G_JGc_TX2_RealLeaves.dictionary D) hash root 1#usize 1#usize 3#usize 4#usize (s03 s) (s04 s) (body03 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGy_G_JGc_TX2_RealLeaves.dictionary D) hash root 1#usize 1#usize 4#usize 5#usize (s04 s) (s05 s) (body04 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGy_G_JGc_TX2_RealLeaves.dictionary D) hash root 1#usize 1#usize 5#usize 6#usize (s05 s) (s06 s) (body05 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGy_G_JGc_TX2_RealLeaves.dictionary D) hash root 1#usize 1#usize 6#usize 7#usize (s06 s) (s07 s) (body06 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGy_G_JGc_TX2_RealLeaves.dictionary D) hash root 1#usize 1#usize 7#usize 8#usize (s07 s) (s08 s) (body07 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGy_G_JGc_TX2_RealLeaves.dictionary D) hash root 1#usize 1#usize 8#usize 9#usize (s08 s) (s09 s) (body08 D hash root s)).trans (
    (JGu_Keys.advance_loop (JGy_G_JGc_TX2_RealLeaves.dictionary D) hash root 1#usize 1#usize 9#usize 10#usize (s09 s) (s10 s) (body09 D hash root s)))))))))))
#print axioms source
end AspisR1.JHh_C_Gu_Scratch1
end

end
