import RPt_JFq_Range
import NDO_JFw_Frames
import JGm_TX2_HeightTools
import NDO_JGm_TX2_View
import NDO_JGy_LightCore
import NDO_JGy_LightPadding
import NDO_JHn_R_JHh_C_Tree0B
import NDO_JHe_SHARealization
import JHn_R_JHh_SmallConstants
section
variable [sha : AspisR1.JHe_SHARealization]
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level0_06
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHe_C_Gr_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes0
def indices00 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
def values00 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 1024#u32 0#usize (encodeState value070) 1952#usize
 def indices01 : List U32 := [512#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value070,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 1460#u32 1#usize (encodeState value071) 1984#usize
 def indices02 : List U32 := [512#u32,730#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value070,encodeState value071,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 2305#u32 2#usize (encodeState value072) 2016#usize
 def indices03 : List U32 := [512#u32,730#u32,1152#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value070,encodeState value071,encodeState value072,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 2497#u32 3#usize (encodeState value073) 2048#usize
 def indices04 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value070,encodeState value071,encodeState value072,encodeState value073,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 2872#u32 4#usize (encodeState value074) 2080#usize
 def indices05 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value070,encodeState value071,encodeState value072,encodeState value073,encodeState value074,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 3004#u32 5#usize (encodeState value075) 2112#usize
 def indices06 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value070,encodeState value071,encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value066,encodeState value067,encodeState value068,encodeState value069]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 3017#u32 6#usize (encodeState value076) 2144#usize
 def indices07 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,3271#u32,3387#u32,3842#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value070,encodeState value071,encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value067,encodeState value068,encodeState value069]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 3271#u32 7#usize (encodeState value077) 2176#usize
 def indices08 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,3387#u32,3842#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value070,encodeState value071,encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value068,encodeState value069]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 3387#u32 8#usize (encodeState value078) 2208#usize
 def indices09 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,3842#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value070,encodeState value071,encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value069]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 3842#u32 9#usize (encodeState value079) 2240#usize
 def indices10 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value070,encodeState value071,encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value070,encodeState value071,encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      1920#usize 1952#usize)=ok (encodeState (JGc_TX2_HashBytes.state [6,240,144,10,89,181,146,35,19,69,34,102,224,239,82,169,126,228,144,157,213,100,223,158,185,74,215,93,123,233,23,161])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 1920#usize 1952#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 1920#usize 1952#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [6,240,144,10,89,181,146,35,19,69,34,102,224,239,82,169,126,228,144,157,213,100,223,158,185,74,215,93,123,233,23,161])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 1920).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30279).take 32)=(encodeState (JGc_TX2_HashBytes.state [6,240,144,10,89,181,146,35,19,69,34,102,224,239,82,169,126,228,144,157,213,100,223,158,185,74,215,93,123,233,23,161])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 1920#usize 1952#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [6,240,144,10,89,181,146,35,19,69,34,102,224,239,82,169,126,228,144,157,213,100,223,158,185,74,215,93,123,233,23,161])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [6,240,144,10,89,181,146,35,19,69,34,102,224,239,82,169,126,228,144,157,213,100,223,158,185,74,215,93,123,233,23,161]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [6,240,144,10,89,181,146,35,19,69,34,102,224,239,82,169,126,228,144,157,213,100,223,158,185,74,215,93,123,233,23,161])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      1952#usize 1984#usize)=ok (encodeState (JGc_TX2_HashBytes.state [90,6,145,42,210,19,190,106,99,39,107,82,176,83,131,93,159,218,108,61,236,10,133,7,20,128,169,78,170,230,90,165])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 1952#usize 1984#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 1952#usize 1984#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [90,6,145,42,210,19,190,106,99,39,107,82,176,83,131,93,159,218,108,61,236,10,133,7,20,128,169,78,170,230,90,165])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 1952).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30311).take 32)=(encodeState (JGc_TX2_HashBytes.state [90,6,145,42,210,19,190,106,99,39,107,82,176,83,131,93,159,218,108,61,236,10,133,7,20,128,169,78,170,230,90,165])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 1952#usize 1984#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [90,6,145,42,210,19,190,106,99,39,107,82,176,83,131,93,159,218,108,61,236,10,133,7,20,128,169,78,170,230,90,165])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [90,6,145,42,210,19,190,106,99,39,107,82,176,83,131,93,159,218,108,61,236,10,133,7,20,128,169,78,170,230,90,165]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [90,6,145,42,210,19,190,106,99,39,107,82,176,83,131,93,159,218,108,61,236,10,133,7,20,128,169,78,170,230,90,165])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      1984#usize 2016#usize)=ok (encodeState (JGc_TX2_HashBytes.state [196,128,247,200,205,132,186,20,133,103,68,116,144,157,48,190,208,40,165,211,155,245,88,90,127,113,249,133,5,38,245,231])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 1984#usize 2016#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 1984#usize 2016#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [196,128,247,200,205,132,186,20,133,103,68,116,144,157,48,190,208,40,165,211,155,245,88,90,127,113,249,133,5,38,245,231])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 1984).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30343).take 32)=(encodeState (JGc_TX2_HashBytes.state [196,128,247,200,205,132,186,20,133,103,68,116,144,157,48,190,208,40,165,211,155,245,88,90,127,113,249,133,5,38,245,231])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 1984#usize 2016#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [196,128,247,200,205,132,186,20,133,103,68,116,144,157,48,190,208,40,165,211,155,245,88,90,127,113,249,133,5,38,245,231])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [196,128,247,200,205,132,186,20,133,103,68,116,144,157,48,190,208,40,165,211,155,245,88,90,127,113,249,133,5,38,245,231]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [196,128,247,200,205,132,186,20,133,103,68,116,144,157,48,190,208,40,165,211,155,245,88,90,127,113,249,133,5,38,245,231])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2016#usize 2048#usize)=ok (encodeState (JGc_TX2_HashBytes.state [2,49,107,237,24,224,109,245,28,116,185,193,147,100,59,21,17,156,87,57,186,102,113,213,3,126,197,123,26,250,39,128])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2016#usize 2048#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2016#usize 2048#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [2,49,107,237,24,224,109,245,28,116,185,193,147,100,59,21,17,156,87,57,186,102,113,213,3,126,197,123,26,250,39,128])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2016).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30375).take 32)=(encodeState (JGc_TX2_HashBytes.state [2,49,107,237,24,224,109,245,28,116,185,193,147,100,59,21,17,156,87,57,186,102,113,213,3,126,197,123,26,250,39,128])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2016#usize 2048#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [2,49,107,237,24,224,109,245,28,116,185,193,147,100,59,21,17,156,87,57,186,102,113,213,3,126,197,123,26,250,39,128])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [2,49,107,237,24,224,109,245,28,116,185,193,147,100,59,21,17,156,87,57,186,102,113,213,3,126,197,123,26,250,39,128]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [2,49,107,237,24,224,109,245,28,116,185,193,147,100,59,21,17,156,87,57,186,102,113,213,3,126,197,123,26,250,39,128])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2048#usize 2080#usize)=ok (encodeState (JGc_TX2_HashBytes.state [136,31,229,129,117,15,123,172,12,255,204,60,56,41,146,141,133,147,183,231,229,23,88,42,114,153,55,180,204,108,193,174])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2048#usize 2080#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2048#usize 2080#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [136,31,229,129,117,15,123,172,12,255,204,60,56,41,146,141,133,147,183,231,229,23,88,42,114,153,55,180,204,108,193,174])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2048).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30407).take 32)=(encodeState (JGc_TX2_HashBytes.state [136,31,229,129,117,15,123,172,12,255,204,60,56,41,146,141,133,147,183,231,229,23,88,42,114,153,55,180,204,108,193,174])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2048#usize 2080#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [136,31,229,129,117,15,123,172,12,255,204,60,56,41,146,141,133,147,183,231,229,23,88,42,114,153,55,180,204,108,193,174])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [136,31,229,129,117,15,123,172,12,255,204,60,56,41,146,141,133,147,183,231,229,23,88,42,114,153,55,180,204,108,193,174]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [136,31,229,129,117,15,123,172,12,255,204,60,56,41,146,141,133,147,183,231,229,23,88,42,114,153,55,180,204,108,193,174])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2080#usize 2112#usize)=ok (encodeState (JGc_TX2_HashBytes.state [34,30,57,86,102,193,213,112,204,200,212,44,184,202,213,35,17,43,57,142,205,70,168,207,70,167,54,101,73,187,97,202])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2080#usize 2112#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2080#usize 2112#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [34,30,57,86,102,193,213,112,204,200,212,44,184,202,213,35,17,43,57,142,205,70,168,207,70,167,54,101,73,187,97,202])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2080).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30439).take 32)=(encodeState (JGc_TX2_HashBytes.state [34,30,57,86,102,193,213,112,204,200,212,44,184,202,213,35,17,43,57,142,205,70,168,207,70,167,54,101,73,187,97,202])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2080#usize 2112#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [34,30,57,86,102,193,213,112,204,200,212,44,184,202,213,35,17,43,57,142,205,70,168,207,70,167,54,101,73,187,97,202])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [34,30,57,86,102,193,213,112,204,200,212,44,184,202,213,35,17,43,57,142,205,70,168,207,70,167,54,101,73,187,97,202]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [34,30,57,86,102,193,213,112,204,200,212,44,184,202,213,35,17,43,57,142,205,70,168,207,70,167,54,101,73,187,97,202])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2112#usize 2144#usize)=ok (encodeState (JGc_TX2_HashBytes.state [92,210,92,203,65,9,235,116,179,182,0,221,48,101,150,142,75,48,236,28,93,37,5,154,73,46,86,46,88,149,55,187])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2112#usize 2144#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2112#usize 2144#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [92,210,92,203,65,9,235,116,179,182,0,221,48,101,150,142,75,48,236,28,93,37,5,154,73,46,86,46,88,149,55,187])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2112).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30471).take 32)=(encodeState (JGc_TX2_HashBytes.state [92,210,92,203,65,9,235,116,179,182,0,221,48,101,150,142,75,48,236,28,93,37,5,154,73,46,86,46,88,149,55,187])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2112#usize 2144#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [92,210,92,203,65,9,235,116,179,182,0,221,48,101,150,142,75,48,236,28,93,37,5,154,73,46,86,46,88,149,55,187])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [92,210,92,203,65,9,235,116,179,182,0,221,48,101,150,142,75,48,236,28,93,37,5,154,73,46,86,46,88,149,55,187]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [92,210,92,203,65,9,235,116,179,182,0,221,48,101,150,142,75,48,236,28,93,37,5,154,73,46,86,46,88,149,55,187])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2144#usize 2176#usize)=ok (encodeState (JGc_TX2_HashBytes.state [205,165,38,151,111,198,79,116,206,226,67,245,236,196,187,100,133,50,31,120,57,157,51,233,222,159,161,218,172,204,11,66])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2144#usize 2176#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2144#usize 2176#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [205,165,38,151,111,198,79,116,206,226,67,245,236,196,187,100,133,50,31,120,57,157,51,233,222,159,161,218,172,204,11,66])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2144).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30503).take 32)=(encodeState (JGc_TX2_HashBytes.state [205,165,38,151,111,198,79,116,206,226,67,245,236,196,187,100,133,50,31,120,57,157,51,233,222,159,161,218,172,204,11,66])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2144#usize 2176#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [205,165,38,151,111,198,79,116,206,226,67,245,236,196,187,100,133,50,31,120,57,157,51,233,222,159,161,218,172,204,11,66])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [205,165,38,151,111,198,79,116,206,226,67,245,236,196,187,100,133,50,31,120,57,157,51,233,222,159,161,218,172,204,11,66]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [205,165,38,151,111,198,79,116,206,226,67,245,236,196,187,100,133,50,31,120,57,157,51,233,222,159,161,218,172,204,11,66])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2176#usize 2208#usize)=ok (encodeState (JGc_TX2_HashBytes.state [226,108,77,28,131,136,7,58,77,240,220,71,105,254,22,209,107,74,73,188,176,248,183,95,174,54,121,81,95,90,24,102])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2176#usize 2208#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2176#usize 2208#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [226,108,77,28,131,136,7,58,77,240,220,71,105,254,22,209,107,74,73,188,176,248,183,95,174,54,121,81,95,90,24,102])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2176).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30535).take 32)=(encodeState (JGc_TX2_HashBytes.state [226,108,77,28,131,136,7,58,77,240,220,71,105,254,22,209,107,74,73,188,176,248,183,95,174,54,121,81,95,90,24,102])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2176#usize 2208#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [226,108,77,28,131,136,7,58,77,240,220,71,105,254,22,209,107,74,73,188,176,248,183,95,174,54,121,81,95,90,24,102])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [226,108,77,28,131,136,7,58,77,240,220,71,105,254,22,209,107,74,73,188,176,248,183,95,174,54,121,81,95,90,24,102]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [226,108,77,28,131,136,7,58,77,240,220,71,105,254,22,209,107,74,73,188,176,248,183,95,174,54,121,81,95,90,24,102])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2208#usize 2240#usize)=ok (encodeState (JGc_TX2_HashBytes.state [87,28,17,1,43,43,239,80,58,175,254,64,102,59,168,121,219,185,145,108,206,67,71,30,115,173,159,96,166,56,54,73])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2208#usize 2240#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2208#usize 2240#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [87,28,17,1,43,43,239,80,58,175,254,64,102,59,168,121,219,185,145,108,206,67,71,30,115,173,159,96,166,56,54,73])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2208).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30567).take 32)=(encodeState (JGc_TX2_HashBytes.state [87,28,17,1,43,43,239,80,58,175,254,64,102,59,168,121,219,185,145,108,206,67,71,30,115,173,159,96,166,56,54,73])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2208#usize 2240#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [87,28,17,1,43,43,239,80,58,175,254,64,102,59,168,121,219,185,145,108,206,67,71,30,115,173,159,96,166,56,54,73])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [87,28,17,1,43,43,239,80,58,175,254,64,102,59,168,121,219,185,145,108,206,67,71,30,115,173,159,96,166,56,54,73]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [87,28,17,1,43,43,239,80,58,175,254,64,102,59,168,121,219,185,145,108,206,67,71,30,115,173,159,96,166,56,54,73])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 1920) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 2240 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 1920 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 1024#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 1920 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value060) :=
    JGm_TX2_View.value (s00 s) indices00 values00 1920 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=1920#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠1024#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1460#u32,JGm_TX2_View.index (s00 s) indices00 values00 1920 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s00 s).«at» 1952#usize)=ok (encodeState (JGc_TX2_HashBytes.state [6,240,144,10,89,181,146,35,19,69,34,102,224,239,82,169,126,228,144,157,213,100,223,158,185,74,215,93,123,233,23,161])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes0 0#usize 0#usize 1#usize 1952#usize 2496#usize
    1024#u32 (encodeState value060) (encodeState (JGc_TX2_HashBytes.state [6,240,144,10,89,181,146,35,19,69,34,102,224,239,82,169,126,228,144,157,213,100,223,158,185,74,215,93,123,233,23,161])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read00
  simp only [show 1024#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls0.source070 D hash (s00 s) 1#usize 1952#usize 1024#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 1952 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 1920 v00
      1024#u32 0#usize (encodeState value070) 1952#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 1460#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 1952 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value061) :=
    JGm_TX2_View.value (s01 s) indices01 values01 1952 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=1952#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠1460#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2305#u32,JGm_TX2_View.index (s01 s) indices01 values01 1952 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s01 s).«at» 1984#usize)=ok (encodeState (JGc_TX2_HashBytes.state [90,6,145,42,210,19,190,106,99,39,107,82,176,83,131,93,159,218,108,61,236,10,133,7,20,128,169,78,170,230,90,165])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes0 1#usize 1#usize 2#usize 1984#usize 2464#usize
    1460#u32 (encodeState value061) (encodeState (JGc_TX2_HashBytes.state [90,6,145,42,210,19,190,106,99,39,107,82,176,83,131,93,159,218,108,61,236,10,133,7,20,128,169,78,170,230,90,165])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read01
  simp only [show 1460#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes0 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls0.source071 D hash (s01 s) 2#usize 1984#usize 1460#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 1984 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 1952 v01
      1460#u32 1#usize (encodeState value071) 1984#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 2305#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 1984 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value062) :=
    JGm_TX2_View.value (s02 s) indices02 values02 1984 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=1984#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠2305#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2497#u32,JGm_TX2_View.index (s02 s) indices02 values02 1984 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s02 s).«at» 2016#usize)=ok (encodeState (JGc_TX2_HashBytes.state [196,128,247,200,205,132,186,20,133,103,68,116,144,157,48,190,208,40,165,211,155,245,88,90,127,113,249,133,5,38,245,231])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes0 2#usize 2#usize 3#usize 2016#usize 2432#usize
    2305#u32 (encodeState value062) (encodeState (JGc_TX2_HashBytes.state [196,128,247,200,205,132,186,20,133,103,68,116,144,157,48,190,208,40,165,211,155,245,88,90,127,113,249,133,5,38,245,231])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read02
  simp only [show 2305#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes0 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls0.source072 D hash (s02 s) 3#usize 2016#usize 2305#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 2016 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 1984 v02
      2305#u32 2#usize (encodeState value072) 2016#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 2497#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 2016 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value063) :=
    JGm_TX2_View.value (s03 s) indices03 values03 2016 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=2016#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠2497#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2872#u32,JGm_TX2_View.index (s03 s) indices03 values03 2016 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s03 s).«at» 2048#usize)=ok (encodeState (JGc_TX2_HashBytes.state [2,49,107,237,24,224,109,245,28,116,185,193,147,100,59,21,17,156,87,57,186,102,113,213,3,126,197,123,26,250,39,128])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes0 3#usize 3#usize 4#usize 2048#usize 2400#usize
    2497#u32 (encodeState value063) (encodeState (JGc_TX2_HashBytes.state [2,49,107,237,24,224,109,245,28,116,185,193,147,100,59,21,17,156,87,57,186,102,113,213,3,126,197,123,26,250,39,128])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read03
  simp only [show 2497#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes0 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls0.source073 D hash (s03 s) 4#usize 2048#usize 2497#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 2048 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 2016 v03
      2497#u32 3#usize (encodeState value073) 2048#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 2872#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 2048 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value064) :=
    JGm_TX2_View.value (s04 s) indices04 values04 2048 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=2048#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠2872#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3004#u32,JGm_TX2_View.index (s04 s) indices04 values04 2048 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s04 s).«at» 2080#usize)=ok (encodeState (JGc_TX2_HashBytes.state [136,31,229,129,117,15,123,172,12,255,204,60,56,41,146,141,133,147,183,231,229,23,88,42,114,153,55,180,204,108,193,174])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes0 4#usize 4#usize 5#usize 2080#usize 2368#usize
    2872#u32 (encodeState value064) (encodeState (JGc_TX2_HashBytes.state [136,31,229,129,117,15,123,172,12,255,204,60,56,41,146,141,133,147,183,231,229,23,88,42,114,153,55,180,204,108,193,174])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read04
  simp only [show 2872#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes0 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls0.source074 D hash (s04 s) 5#usize 2080#usize 2872#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 2080 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 2048 v04
      2872#u32 4#usize (encodeState value074) 2080#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 3004#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 2080 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value065) :=
    JGm_TX2_View.value (s05 s) indices05 values05 2080 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=2080#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠3004#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3017#u32,JGm_TX2_View.index (s05 s) indices05 values05 2080 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s05 s).«at» 2112#usize)=ok (encodeState (JGc_TX2_HashBytes.state [34,30,57,86,102,193,213,112,204,200,212,44,184,202,213,35,17,43,57,142,205,70,168,207,70,167,54,101,73,187,97,202])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes0 5#usize 5#usize 6#usize 2112#usize 2336#usize
    3004#u32 (encodeState value065) (encodeState (JGc_TX2_HashBytes.state [34,30,57,86,102,193,213,112,204,200,212,44,184,202,213,35,17,43,57,142,205,70,168,207,70,167,54,101,73,187,97,202])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read05
  simp only [show 3004#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes0 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls0.source075 D hash (s05 s) 6#usize 2112#usize 3004#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 2112 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 2080 v05
      3004#u32 5#usize (encodeState value075) 2112#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 3017#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 2112 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value066) :=
    JGm_TX2_View.value (s06 s) indices06 values06 2112 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=2112#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠3017#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3271#u32,JGm_TX2_View.index (s06 s) indices06 values06 2112 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s06 s).«at» 2144#usize)=ok (encodeState (JGc_TX2_HashBytes.state [92,210,92,203,65,9,235,116,179,182,0,221,48,101,150,142,75,48,236,28,93,37,5,154,73,46,86,46,88,149,55,187])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes0 6#usize 6#usize 7#usize 2144#usize 2304#usize
    3017#u32 (encodeState value066) (encodeState (JGc_TX2_HashBytes.state [92,210,92,203,65,9,235,116,179,182,0,221,48,101,150,142,75,48,236,28,93,37,5,154,73,46,86,46,88,149,55,187])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read06
  simp only [show 3017#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes0 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls0.source076 D hash (s06 s) 7#usize 2144#usize 3017#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 2144 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 2112 v06
      3017#u32 6#usize (encodeState value076) 2144#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 3271#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 2144 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value067) :=
    JGm_TX2_View.value (s07 s) indices07 values07 2144 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=2144#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠3271#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3387#u32,JGm_TX2_View.index (s07 s) indices07 values07 2144 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s07 s).«at» 2176#usize)=ok (encodeState (JGc_TX2_HashBytes.state [205,165,38,151,111,198,79,116,206,226,67,245,236,196,187,100,133,50,31,120,57,157,51,233,222,159,161,218,172,204,11,66])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes0 7#usize 7#usize 8#usize 2176#usize 2272#usize
    3271#u32 (encodeState value067) (encodeState (JGc_TX2_HashBytes.state [205,165,38,151,111,198,79,116,206,226,67,245,236,196,187,100,133,50,31,120,57,157,51,233,222,159,161,218,172,204,11,66])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read07
  simp only [show 3271#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes0 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls0.source077 D hash (s07 s) 8#usize 2176#usize 3271#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 2176 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 2144 v07
      3271#u32 7#usize (encodeState value077) 2176#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 3387#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 2176 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value068) :=
    JGm_TX2_View.value (s08 s) indices08 values08 2176 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=2176#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠3387#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3842#u32,JGm_TX2_View.index (s08 s) indices08 values08 2176 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s08 s).«at» 2208#usize)=ok (encodeState (JGc_TX2_HashBytes.state [226,108,77,28,131,136,7,58,77,240,220,71,105,254,22,209,107,74,73,188,176,248,183,95,174,54,121,81,95,90,24,102])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes0 8#usize 8#usize 9#usize 2208#usize 2240#usize
    3387#u32 (encodeState value068) (encodeState (JGc_TX2_HashBytes.state [226,108,77,28,131,136,7,58,77,240,220,71,105,254,22,209,107,74,73,188,176,248,183,95,174,54,121,81,95,90,24,102])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read08
  simp only [show 3387#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes0 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls0.source078 D hash (s08 s) 9#usize 2208#usize 3387#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 2208 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 2176 v08
      3387#u32 8#usize (encodeState value078) 2208#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 3842#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 2208 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value069) :=
    JGm_TX2_View.value (s09 s) indices09 values09 2208 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=2208#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠3842#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s09 s).«at» 2240#usize)=ok (encodeState (JGc_TX2_HashBytes.state [87,28,17,1,43,43,239,80,58,175,254,64,102,59,168,121,219,185,145,108,206,67,71,30,115,173,159,96,166,56,54,73])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes0 9#usize 9#usize 10#usize 2240#usize 2208#usize
    3842#u32 (encodeState value069) (encodeState (JGc_TX2_HashBytes.state [87,28,17,1,43,43,239,80,58,175,254,64,102,59,168,121,219,185,145,108,206,67,71,30,115,173,159,96,166,56,54,73])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read09
  simp only [show 3842#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes0 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls0.source079 D hash (s09 s) 10#usize 2240#usize 3842#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 2240 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 2208 v09
      3842#u32 9#usize (encodeState value079) 2240#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes0 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes0 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes0 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes0 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes0 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes0 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes0 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes0 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes0 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes0 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes0 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 2240
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level0_06
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level0_07
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHe_C_Gr_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes0
def indices00 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
def values00 : List (Array U8 32#usize) := [encodeState value070,encodeState value071,encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 512#u32 0#usize (encodeState value080) 2272#usize
 def indices01 : List U32 := [256#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value080,encodeState value071,encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 730#u32 1#usize (encodeState value081) 2304#usize
 def indices02 : List U32 := [256#u32,365#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value080,encodeState value081,encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 1152#u32 2#usize (encodeState value082) 2336#usize
 def indices03 : List U32 := [256#u32,365#u32,576#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value080,encodeState value081,encodeState value082,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 1248#u32 3#usize (encodeState value083) 2368#usize
 def indices04 : List U32 := [256#u32,365#u32,576#u32,624#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value080,encodeState value081,encodeState value082,encodeState value083,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 1436#u32 4#usize (encodeState value084) 2400#usize
 def indices05 : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value080,encodeState value081,encodeState value082,encodeState value083,encodeState value084,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 1502#u32 5#usize (encodeState value085) 2432#usize
 def indices06 : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,751#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value080,encodeState value081,encodeState value082,encodeState value083,encodeState value084,encodeState value085,encodeState value076,encodeState value077,encodeState value078,encodeState value079]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 1508#u32 6#usize (encodeState value086) 2464#usize
 def indices07 : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,751#u32,754#u32,1635#u32,1693#u32,1921#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value080,encodeState value081,encodeState value082,encodeState value083,encodeState value084,encodeState value085,encodeState value086,encodeState value077,encodeState value078,encodeState value079]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 1635#u32 7#usize (encodeState value087) 2496#usize
 def indices08 : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,751#u32,754#u32,817#u32,1693#u32,1921#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value080,encodeState value081,encodeState value082,encodeState value083,encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value078,encodeState value079]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 1693#u32 8#usize (encodeState value088) 2528#usize
 def indices09 : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,751#u32,754#u32,817#u32,846#u32,1921#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value080,encodeState value081,encodeState value082,encodeState value083,encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value079]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 1921#u32 9#usize (encodeState value089) 2560#usize
 def indices10 : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,751#u32,754#u32,817#u32,846#u32,960#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value080,encodeState value081,encodeState value082,encodeState value083,encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,751#u32,754#u32,817#u32,846#u32,960#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value080,encodeState value081,encodeState value082,encodeState value083,encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2240#usize 2272#usize)=ok (encodeState (JGc_TX2_HashBytes.state [77,170,189,130,235,22,61,148,149,65,163,235,1,168,255,7,23,41,163,194,92,20,52,96,214,215,10,79,81,125,23,74])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2240#usize 2272#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2240#usize 2272#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [77,170,189,130,235,22,61,148,149,65,163,235,1,168,255,7,23,41,163,194,92,20,52,96,214,215,10,79,81,125,23,74])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2240).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30599).take 32)=(encodeState (JGc_TX2_HashBytes.state [77,170,189,130,235,22,61,148,149,65,163,235,1,168,255,7,23,41,163,194,92,20,52,96,214,215,10,79,81,125,23,74])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2240#usize 2272#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [77,170,189,130,235,22,61,148,149,65,163,235,1,168,255,7,23,41,163,194,92,20,52,96,214,215,10,79,81,125,23,74])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [77,170,189,130,235,22,61,148,149,65,163,235,1,168,255,7,23,41,163,194,92,20,52,96,214,215,10,79,81,125,23,74]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [77,170,189,130,235,22,61,148,149,65,163,235,1,168,255,7,23,41,163,194,92,20,52,96,214,215,10,79,81,125,23,74])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2272#usize 2304#usize)=ok (encodeState (JGc_TX2_HashBytes.state [220,4,163,99,213,83,228,35,211,78,46,27,57,83,108,166,235,71,20,58,174,254,18,51,47,16,101,29,62,46,59,127])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2272#usize 2304#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2272#usize 2304#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [220,4,163,99,213,83,228,35,211,78,46,27,57,83,108,166,235,71,20,58,174,254,18,51,47,16,101,29,62,46,59,127])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2272).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30631).take 32)=(encodeState (JGc_TX2_HashBytes.state [220,4,163,99,213,83,228,35,211,78,46,27,57,83,108,166,235,71,20,58,174,254,18,51,47,16,101,29,62,46,59,127])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2272#usize 2304#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [220,4,163,99,213,83,228,35,211,78,46,27,57,83,108,166,235,71,20,58,174,254,18,51,47,16,101,29,62,46,59,127])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [220,4,163,99,213,83,228,35,211,78,46,27,57,83,108,166,235,71,20,58,174,254,18,51,47,16,101,29,62,46,59,127]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [220,4,163,99,213,83,228,35,211,78,46,27,57,83,108,166,235,71,20,58,174,254,18,51,47,16,101,29,62,46,59,127])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2304#usize 2336#usize)=ok (encodeState (JGc_TX2_HashBytes.state [8,32,93,135,247,254,167,22,175,205,245,1,51,185,169,99,158,32,144,204,248,6,73,82,86,253,11,31,112,23,182,248])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2304#usize 2336#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2304#usize 2336#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [8,32,93,135,247,254,167,22,175,205,245,1,51,185,169,99,158,32,144,204,248,6,73,82,86,253,11,31,112,23,182,248])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2304).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30663).take 32)=(encodeState (JGc_TX2_HashBytes.state [8,32,93,135,247,254,167,22,175,205,245,1,51,185,169,99,158,32,144,204,248,6,73,82,86,253,11,31,112,23,182,248])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2304#usize 2336#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [8,32,93,135,247,254,167,22,175,205,245,1,51,185,169,99,158,32,144,204,248,6,73,82,86,253,11,31,112,23,182,248])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [8,32,93,135,247,254,167,22,175,205,245,1,51,185,169,99,158,32,144,204,248,6,73,82,86,253,11,31,112,23,182,248]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [8,32,93,135,247,254,167,22,175,205,245,1,51,185,169,99,158,32,144,204,248,6,73,82,86,253,11,31,112,23,182,248])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2336#usize 2368#usize)=ok (encodeState (JGc_TX2_HashBytes.state [237,7,29,17,196,126,123,186,28,187,171,89,156,231,137,55,83,50,16,209,36,156,194,167,84,36,109,35,86,123,184,82])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2336#usize 2368#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2336#usize 2368#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [237,7,29,17,196,126,123,186,28,187,171,89,156,231,137,55,83,50,16,209,36,156,194,167,84,36,109,35,86,123,184,82])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2336).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30695).take 32)=(encodeState (JGc_TX2_HashBytes.state [237,7,29,17,196,126,123,186,28,187,171,89,156,231,137,55,83,50,16,209,36,156,194,167,84,36,109,35,86,123,184,82])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2336#usize 2368#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [237,7,29,17,196,126,123,186,28,187,171,89,156,231,137,55,83,50,16,209,36,156,194,167,84,36,109,35,86,123,184,82])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [237,7,29,17,196,126,123,186,28,187,171,89,156,231,137,55,83,50,16,209,36,156,194,167,84,36,109,35,86,123,184,82]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [237,7,29,17,196,126,123,186,28,187,171,89,156,231,137,55,83,50,16,209,36,156,194,167,84,36,109,35,86,123,184,82])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2368#usize 2400#usize)=ok (encodeState (JGc_TX2_HashBytes.state [164,143,95,212,102,248,18,5,14,206,35,160,137,216,216,140,138,220,155,8,95,80,232,194,90,93,3,211,167,239,202,54])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2368#usize 2400#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2368#usize 2400#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [164,143,95,212,102,248,18,5,14,206,35,160,137,216,216,140,138,220,155,8,95,80,232,194,90,93,3,211,167,239,202,54])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2368).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30727).take 32)=(encodeState (JGc_TX2_HashBytes.state [164,143,95,212,102,248,18,5,14,206,35,160,137,216,216,140,138,220,155,8,95,80,232,194,90,93,3,211,167,239,202,54])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2368#usize 2400#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [164,143,95,212,102,248,18,5,14,206,35,160,137,216,216,140,138,220,155,8,95,80,232,194,90,93,3,211,167,239,202,54])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [164,143,95,212,102,248,18,5,14,206,35,160,137,216,216,140,138,220,155,8,95,80,232,194,90,93,3,211,167,239,202,54]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [164,143,95,212,102,248,18,5,14,206,35,160,137,216,216,140,138,220,155,8,95,80,232,194,90,93,3,211,167,239,202,54])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2400#usize 2432#usize)=ok (encodeState (JGc_TX2_HashBytes.state [112,33,7,3,28,71,221,2,47,93,159,111,101,209,164,115,182,37,12,24,179,5,186,191,241,44,19,167,238,76,32,192])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2400#usize 2432#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2400#usize 2432#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [112,33,7,3,28,71,221,2,47,93,159,111,101,209,164,115,182,37,12,24,179,5,186,191,241,44,19,167,238,76,32,192])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2400).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30759).take 32)=(encodeState (JGc_TX2_HashBytes.state [112,33,7,3,28,71,221,2,47,93,159,111,101,209,164,115,182,37,12,24,179,5,186,191,241,44,19,167,238,76,32,192])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2400#usize 2432#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [112,33,7,3,28,71,221,2,47,93,159,111,101,209,164,115,182,37,12,24,179,5,186,191,241,44,19,167,238,76,32,192])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [112,33,7,3,28,71,221,2,47,93,159,111,101,209,164,115,182,37,12,24,179,5,186,191,241,44,19,167,238,76,32,192]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [112,33,7,3,28,71,221,2,47,93,159,111,101,209,164,115,182,37,12,24,179,5,186,191,241,44,19,167,238,76,32,192])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2432#usize 2464#usize)=ok (encodeState (JGc_TX2_HashBytes.state [74,175,62,170,208,166,232,20,189,64,80,118,215,50,80,8,224,151,209,81,20,7,185,85,124,62,24,188,176,43,92,225])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2432#usize 2464#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2432#usize 2464#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [74,175,62,170,208,166,232,20,189,64,80,118,215,50,80,8,224,151,209,81,20,7,185,85,124,62,24,188,176,43,92,225])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2432).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30791).take 32)=(encodeState (JGc_TX2_HashBytes.state [74,175,62,170,208,166,232,20,189,64,80,118,215,50,80,8,224,151,209,81,20,7,185,85,124,62,24,188,176,43,92,225])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2432#usize 2464#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [74,175,62,170,208,166,232,20,189,64,80,118,215,50,80,8,224,151,209,81,20,7,185,85,124,62,24,188,176,43,92,225])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [74,175,62,170,208,166,232,20,189,64,80,118,215,50,80,8,224,151,209,81,20,7,185,85,124,62,24,188,176,43,92,225]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [74,175,62,170,208,166,232,20,189,64,80,118,215,50,80,8,224,151,209,81,20,7,185,85,124,62,24,188,176,43,92,225])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2464#usize 2496#usize)=ok (encodeState (JGc_TX2_HashBytes.state [218,253,65,240,172,229,138,129,76,204,176,47,148,25,169,129,220,198,33,211,14,132,216,254,101,36,143,228,205,218,132,45])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2464#usize 2496#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2464#usize 2496#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [218,253,65,240,172,229,138,129,76,204,176,47,148,25,169,129,220,198,33,211,14,132,216,254,101,36,143,228,205,218,132,45])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2464).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30823).take 32)=(encodeState (JGc_TX2_HashBytes.state [218,253,65,240,172,229,138,129,76,204,176,47,148,25,169,129,220,198,33,211,14,132,216,254,101,36,143,228,205,218,132,45])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2464#usize 2496#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [218,253,65,240,172,229,138,129,76,204,176,47,148,25,169,129,220,198,33,211,14,132,216,254,101,36,143,228,205,218,132,45])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [218,253,65,240,172,229,138,129,76,204,176,47,148,25,169,129,220,198,33,211,14,132,216,254,101,36,143,228,205,218,132,45]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [218,253,65,240,172,229,138,129,76,204,176,47,148,25,169,129,220,198,33,211,14,132,216,254,101,36,143,228,205,218,132,45])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2496#usize 2528#usize)=ok (encodeState (JGc_TX2_HashBytes.state [92,111,165,106,142,29,249,211,6,148,240,59,145,1,129,21,239,41,72,97,151,216,109,27,177,211,241,204,132,133,92,249])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2496#usize 2528#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2496#usize 2528#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [92,111,165,106,142,29,249,211,6,148,240,59,145,1,129,21,239,41,72,97,151,216,109,27,177,211,241,204,132,133,92,249])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2496).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30855).take 32)=(encodeState (JGc_TX2_HashBytes.state [92,111,165,106,142,29,249,211,6,148,240,59,145,1,129,21,239,41,72,97,151,216,109,27,177,211,241,204,132,133,92,249])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2496#usize 2528#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [92,111,165,106,142,29,249,211,6,148,240,59,145,1,129,21,239,41,72,97,151,216,109,27,177,211,241,204,132,133,92,249])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [92,111,165,106,142,29,249,211,6,148,240,59,145,1,129,21,239,41,72,97,151,216,109,27,177,211,241,204,132,133,92,249]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [92,111,165,106,142,29,249,211,6,148,240,59,145,1,129,21,239,41,72,97,151,216,109,27,177,211,241,204,132,133,92,249])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2528#usize 2560#usize)=ok (encodeState (JGc_TX2_HashBytes.state [15,149,178,185,103,188,80,183,213,234,175,109,95,91,156,29,122,205,226,127,154,135,172,211,157,76,137,128,192,230,142,182])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2528#usize 2560#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2528#usize 2560#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [15,149,178,185,103,188,80,183,213,234,175,109,95,91,156,29,122,205,226,127,154,135,172,211,157,76,137,128,192,230,142,182])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2528).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30887).take 32)=(encodeState (JGc_TX2_HashBytes.state [15,149,178,185,103,188,80,183,213,234,175,109,95,91,156,29,122,205,226,127,154,135,172,211,157,76,137,128,192,230,142,182])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2528#usize 2560#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [15,149,178,185,103,188,80,183,213,234,175,109,95,91,156,29,122,205,226,127,154,135,172,211,157,76,137,128,192,230,142,182])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [15,149,178,185,103,188,80,183,213,234,175,109,95,91,156,29,122,205,226,127,154,135,172,211,157,76,137,128,192,230,142,182]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [15,149,178,185,103,188,80,183,213,234,175,109,95,91,156,29,122,205,226,127,154,135,172,211,157,76,137,128,192,230,142,182])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 2240) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 2560 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 2240 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 512#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 2240 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value070) :=
    JGm_TX2_View.value (s00 s) indices00 values00 2240 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=2240#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠512#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨730#u32,JGm_TX2_View.index (s00 s) indices00 values00 2240 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s00 s).«at» 2272#usize)=ok (encodeState (JGc_TX2_HashBytes.state [77,170,189,130,235,22,61,148,149,65,163,235,1,168,255,7,23,41,163,194,92,20,52,96,214,215,10,79,81,125,23,74])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes0 0#usize 0#usize 1#usize 2272#usize 2176#usize
    512#u32 (encodeState value070) (encodeState (JGc_TX2_HashBytes.state [77,170,189,130,235,22,61,148,149,65,163,235,1,168,255,7,23,41,163,194,92,20,52,96,214,215,10,79,81,125,23,74])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read00
  simp only [show 512#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls0.source080 D hash (s00 s) 1#usize 2272#usize 512#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 2272 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 2240 v00
      512#u32 0#usize (encodeState value080) 2272#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 730#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 2272 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value071) :=
    JGm_TX2_View.value (s01 s) indices01 values01 2272 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=2272#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠730#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1152#u32,JGm_TX2_View.index (s01 s) indices01 values01 2272 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s01 s).«at» 2304#usize)=ok (encodeState (JGc_TX2_HashBytes.state [220,4,163,99,213,83,228,35,211,78,46,27,57,83,108,166,235,71,20,58,174,254,18,51,47,16,101,29,62,46,59,127])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes0 1#usize 1#usize 2#usize 2304#usize 2144#usize
    730#u32 (encodeState value071) (encodeState (JGc_TX2_HashBytes.state [220,4,163,99,213,83,228,35,211,78,46,27,57,83,108,166,235,71,20,58,174,254,18,51,47,16,101,29,62,46,59,127])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read01
  simp only [show 730#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes0 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls0.source081 D hash (s01 s) 2#usize 2304#usize 730#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 2304 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 2272 v01
      730#u32 1#usize (encodeState value081) 2304#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 1152#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 2304 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value072) :=
    JGm_TX2_View.value (s02 s) indices02 values02 2304 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=2304#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠1152#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1248#u32,JGm_TX2_View.index (s02 s) indices02 values02 2304 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s02 s).«at» 2336#usize)=ok (encodeState (JGc_TX2_HashBytes.state [8,32,93,135,247,254,167,22,175,205,245,1,51,185,169,99,158,32,144,204,248,6,73,82,86,253,11,31,112,23,182,248])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes0 2#usize 2#usize 3#usize 2336#usize 2112#usize
    1152#u32 (encodeState value072) (encodeState (JGc_TX2_HashBytes.state [8,32,93,135,247,254,167,22,175,205,245,1,51,185,169,99,158,32,144,204,248,6,73,82,86,253,11,31,112,23,182,248])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read02
  simp only [show 1152#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes0 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls0.source082 D hash (s02 s) 3#usize 2336#usize 1152#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 2336 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 2304 v02
      1152#u32 2#usize (encodeState value082) 2336#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 1248#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 2336 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value073) :=
    JGm_TX2_View.value (s03 s) indices03 values03 2336 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=2336#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠1248#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1436#u32,JGm_TX2_View.index (s03 s) indices03 values03 2336 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s03 s).«at» 2368#usize)=ok (encodeState (JGc_TX2_HashBytes.state [237,7,29,17,196,126,123,186,28,187,171,89,156,231,137,55,83,50,16,209,36,156,194,167,84,36,109,35,86,123,184,82])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes0 3#usize 3#usize 4#usize 2368#usize 2080#usize
    1248#u32 (encodeState value073) (encodeState (JGc_TX2_HashBytes.state [237,7,29,17,196,126,123,186,28,187,171,89,156,231,137,55,83,50,16,209,36,156,194,167,84,36,109,35,86,123,184,82])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read03
  simp only [show 1248#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes0 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls0.source083 D hash (s03 s) 4#usize 2368#usize 1248#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 2368 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 2336 v03
      1248#u32 3#usize (encodeState value083) 2368#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 1436#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 2368 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value074) :=
    JGm_TX2_View.value (s04 s) indices04 values04 2368 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=2368#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠1436#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1502#u32,JGm_TX2_View.index (s04 s) indices04 values04 2368 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s04 s).«at» 2400#usize)=ok (encodeState (JGc_TX2_HashBytes.state [164,143,95,212,102,248,18,5,14,206,35,160,137,216,216,140,138,220,155,8,95,80,232,194,90,93,3,211,167,239,202,54])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes0 4#usize 4#usize 5#usize 2400#usize 2048#usize
    1436#u32 (encodeState value074) (encodeState (JGc_TX2_HashBytes.state [164,143,95,212,102,248,18,5,14,206,35,160,137,216,216,140,138,220,155,8,95,80,232,194,90,93,3,211,167,239,202,54])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read04
  simp only [show 1436#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes0 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls0.source084 D hash (s04 s) 5#usize 2400#usize 1436#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 2400 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 2368 v04
      1436#u32 4#usize (encodeState value084) 2400#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 1502#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 2400 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value075) :=
    JGm_TX2_View.value (s05 s) indices05 values05 2400 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=2400#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠1502#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1508#u32,JGm_TX2_View.index (s05 s) indices05 values05 2400 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s05 s).«at» 2432#usize)=ok (encodeState (JGc_TX2_HashBytes.state [112,33,7,3,28,71,221,2,47,93,159,111,101,209,164,115,182,37,12,24,179,5,186,191,241,44,19,167,238,76,32,192])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes0 5#usize 5#usize 6#usize 2432#usize 2016#usize
    1502#u32 (encodeState value075) (encodeState (JGc_TX2_HashBytes.state [112,33,7,3,28,71,221,2,47,93,159,111,101,209,164,115,182,37,12,24,179,5,186,191,241,44,19,167,238,76,32,192])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read05
  simp only [show 1502#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes0 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls0.source085 D hash (s05 s) 6#usize 2432#usize 1502#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 2432 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 2400 v05
      1502#u32 5#usize (encodeState value085) 2432#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 1508#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 2432 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value076) :=
    JGm_TX2_View.value (s06 s) indices06 values06 2432 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=2432#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠1508#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1635#u32,JGm_TX2_View.index (s06 s) indices06 values06 2432 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s06 s).«at» 2464#usize)=ok (encodeState (JGc_TX2_HashBytes.state [74,175,62,170,208,166,232,20,189,64,80,118,215,50,80,8,224,151,209,81,20,7,185,85,124,62,24,188,176,43,92,225])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes0 6#usize 6#usize 7#usize 2464#usize 1984#usize
    1508#u32 (encodeState value076) (encodeState (JGc_TX2_HashBytes.state [74,175,62,170,208,166,232,20,189,64,80,118,215,50,80,8,224,151,209,81,20,7,185,85,124,62,24,188,176,43,92,225])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read06
  simp only [show 1508#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes0 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls0.source086 D hash (s06 s) 7#usize 2464#usize 1508#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 2464 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 2432 v06
      1508#u32 6#usize (encodeState value086) 2464#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 1635#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 2464 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value077) :=
    JGm_TX2_View.value (s07 s) indices07 values07 2464 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=2464#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠1635#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1693#u32,JGm_TX2_View.index (s07 s) indices07 values07 2464 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s07 s).«at» 2496#usize)=ok (encodeState (JGc_TX2_HashBytes.state [218,253,65,240,172,229,138,129,76,204,176,47,148,25,169,129,220,198,33,211,14,132,216,254,101,36,143,228,205,218,132,45])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes0 7#usize 7#usize 8#usize 2496#usize 1952#usize
    1635#u32 (encodeState value077) (encodeState (JGc_TX2_HashBytes.state [218,253,65,240,172,229,138,129,76,204,176,47,148,25,169,129,220,198,33,211,14,132,216,254,101,36,143,228,205,218,132,45])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read07
  simp only [show 1635#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes0 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls0.source087 D hash (s07 s) 8#usize 2496#usize 1635#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 2496 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 2464 v07
      1635#u32 7#usize (encodeState value087) 2496#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 1693#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 2496 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value078) :=
    JGm_TX2_View.value (s08 s) indices08 values08 2496 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=2496#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠1693#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1921#u32,JGm_TX2_View.index (s08 s) indices08 values08 2496 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s08 s).«at» 2528#usize)=ok (encodeState (JGc_TX2_HashBytes.state [92,111,165,106,142,29,249,211,6,148,240,59,145,1,129,21,239,41,72,97,151,216,109,27,177,211,241,204,132,133,92,249])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes0 8#usize 8#usize 9#usize 2528#usize 1920#usize
    1693#u32 (encodeState value078) (encodeState (JGc_TX2_HashBytes.state [92,111,165,106,142,29,249,211,6,148,240,59,145,1,129,21,239,41,72,97,151,216,109,27,177,211,241,204,132,133,92,249])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read08
  simp only [show 1693#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes0 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls0.source088 D hash (s08 s) 9#usize 2528#usize 1693#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 2528 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 2496 v08
      1693#u32 8#usize (encodeState value088) 2528#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 1921#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 2528 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value079) :=
    JGm_TX2_View.value (s09 s) indices09 values09 2528 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=2528#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠1921#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s09 s).«at» 2560#usize)=ok (encodeState (JGc_TX2_HashBytes.state [15,149,178,185,103,188,80,183,213,234,175,109,95,91,156,29,122,205,226,127,154,135,172,211,157,76,137,128,192,230,142,182])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes0 9#usize 9#usize 10#usize 2560#usize 1888#usize
    1921#u32 (encodeState value079) (encodeState (JGc_TX2_HashBytes.state [15,149,178,185,103,188,80,183,213,234,175,109,95,91,156,29,122,205,226,127,154,135,172,211,157,76,137,128,192,230,142,182])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read09
  simp only [show 1921#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes0 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls0.source089 D hash (s09 s) 10#usize 2560#usize 1921#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 2560 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 2528 v09
      1921#u32 9#usize (encodeState value089) 2560#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes0 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes0 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes0 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes0 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes0 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes0 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes0 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes0 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes0 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes0 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes0 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 2560
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level0_07
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level0_08
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHe_C_Gr_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes0
def indices00 : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,751#u32,754#u32,817#u32,846#u32,960#u32]
def values00 : List (Array U8 32#usize) := [encodeState value080,encodeState value081,encodeState value082,encodeState value083,encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 256#u32 0#usize (encodeState value090) 2592#usize
 def indices01 : List U32 := [128#u32,365#u32,576#u32,624#u32,718#u32,751#u32,754#u32,817#u32,846#u32,960#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value090,encodeState value081,encodeState value082,encodeState value083,encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 365#u32 1#usize (encodeState value091) 2624#usize
 def indices02 : List U32 := [128#u32,182#u32,576#u32,624#u32,718#u32,751#u32,754#u32,817#u32,846#u32,960#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value090,encodeState value091,encodeState value082,encodeState value083,encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 576#u32 2#usize (encodeState value092) 2656#usize
 def indices03 : List U32 := [128#u32,182#u32,288#u32,624#u32,718#u32,751#u32,754#u32,817#u32,846#u32,960#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value090,encodeState value091,encodeState value092,encodeState value083,encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 624#u32 3#usize (encodeState value093) 2688#usize
 def indices04 : List U32 := [128#u32,182#u32,288#u32,312#u32,718#u32,751#u32,754#u32,817#u32,846#u32,960#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 718#u32 4#usize (encodeState value094) 2720#usize
 def indices05 : List U32 := [128#u32,182#u32,288#u32,312#u32,359#u32,751#u32,754#u32,817#u32,846#u32,960#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 751#u32 5#usize (encodeState value095) 2752#usize
 def indices06 : List U32 := [128#u32,182#u32,288#u32,312#u32,359#u32,375#u32,754#u32,817#u32,846#u32,960#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095,encodeState value086,encodeState value087,encodeState value088,encodeState value089]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 754#u32 6#usize (encodeState value096) 2784#usize
 def indices07 : List U32 := [128#u32,182#u32,288#u32,312#u32,359#u32,375#u32,377#u32,817#u32,846#u32,960#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095,encodeState value096,encodeState value087,encodeState value088,encodeState value089]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 817#u32 7#usize (encodeState value097) 2816#usize
 def indices08 : List U32 := [128#u32,182#u32,288#u32,312#u32,359#u32,375#u32,377#u32,408#u32,846#u32,960#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095,encodeState value096,encodeState value097,encodeState value088,encodeState value089]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 846#u32 8#usize (encodeState value098) 2848#usize
 def indices09 : List U32 := [128#u32,182#u32,288#u32,312#u32,359#u32,375#u32,377#u32,408#u32,423#u32,960#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095,encodeState value096,encodeState value097,encodeState value098,encodeState value089]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 960#u32 9#usize (encodeState value099) 2880#usize
 def indices10 : List U32 := [128#u32,182#u32,288#u32,312#u32,359#u32,375#u32,377#u32,408#u32,423#u32,480#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095,encodeState value096,encodeState value097,encodeState value098,encodeState value099]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [128#u32,182#u32,288#u32,312#u32,359#u32,375#u32,377#u32,408#u32,423#u32,480#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095,encodeState value096,encodeState value097,encodeState value098,encodeState value099]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2560#usize 2592#usize)=ok (encodeState (JGc_TX2_HashBytes.state [113,23,49,153,65,62,50,121,121,134,77,85,4,221,172,58,119,143,25,248,30,111,211,227,9,191,95,71,39,81,225,50])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2560#usize 2592#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2560#usize 2592#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [113,23,49,153,65,62,50,121,121,134,77,85,4,221,172,58,119,143,25,248,30,111,211,227,9,191,95,71,39,81,225,50])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2560).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30919).take 32)=(encodeState (JGc_TX2_HashBytes.state [113,23,49,153,65,62,50,121,121,134,77,85,4,221,172,58,119,143,25,248,30,111,211,227,9,191,95,71,39,81,225,50])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2560#usize 2592#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [113,23,49,153,65,62,50,121,121,134,77,85,4,221,172,58,119,143,25,248,30,111,211,227,9,191,95,71,39,81,225,50])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [113,23,49,153,65,62,50,121,121,134,77,85,4,221,172,58,119,143,25,248,30,111,211,227,9,191,95,71,39,81,225,50]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [113,23,49,153,65,62,50,121,121,134,77,85,4,221,172,58,119,143,25,248,30,111,211,227,9,191,95,71,39,81,225,50])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2592#usize 2624#usize)=ok (encodeState (JGc_TX2_HashBytes.state [17,86,79,88,53,63,109,64,216,191,11,30,55,109,89,48,69,42,142,22,51,233,130,145,169,63,100,38,75,249,74,19])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2592#usize 2624#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2592#usize 2624#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [17,86,79,88,53,63,109,64,216,191,11,30,55,109,89,48,69,42,142,22,51,233,130,145,169,63,100,38,75,249,74,19])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2592).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30951).take 32)=(encodeState (JGc_TX2_HashBytes.state [17,86,79,88,53,63,109,64,216,191,11,30,55,109,89,48,69,42,142,22,51,233,130,145,169,63,100,38,75,249,74,19])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2592#usize 2624#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [17,86,79,88,53,63,109,64,216,191,11,30,55,109,89,48,69,42,142,22,51,233,130,145,169,63,100,38,75,249,74,19])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [17,86,79,88,53,63,109,64,216,191,11,30,55,109,89,48,69,42,142,22,51,233,130,145,169,63,100,38,75,249,74,19]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [17,86,79,88,53,63,109,64,216,191,11,30,55,109,89,48,69,42,142,22,51,233,130,145,169,63,100,38,75,249,74,19])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2624#usize 2656#usize)=ok (encodeState (JGc_TX2_HashBytes.state [226,155,182,235,137,88,156,193,14,203,121,8,103,202,235,239,155,117,229,172,214,169,41,35,14,166,228,96,191,226,79,63])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2624#usize 2656#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2624#usize 2656#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [226,155,182,235,137,88,156,193,14,203,121,8,103,202,235,239,155,117,229,172,214,169,41,35,14,166,228,96,191,226,79,63])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2624).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 30983).take 32)=(encodeState (JGc_TX2_HashBytes.state [226,155,182,235,137,88,156,193,14,203,121,8,103,202,235,239,155,117,229,172,214,169,41,35,14,166,228,96,191,226,79,63])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2624#usize 2656#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [226,155,182,235,137,88,156,193,14,203,121,8,103,202,235,239,155,117,229,172,214,169,41,35,14,166,228,96,191,226,79,63])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [226,155,182,235,137,88,156,193,14,203,121,8,103,202,235,239,155,117,229,172,214,169,41,35,14,166,228,96,191,226,79,63]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [226,155,182,235,137,88,156,193,14,203,121,8,103,202,235,239,155,117,229,172,214,169,41,35,14,166,228,96,191,226,79,63])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2656#usize 2688#usize)=ok (encodeState (JGc_TX2_HashBytes.state [126,121,251,104,220,255,47,155,0,110,75,75,75,176,125,193,113,66,44,179,9,60,208,17,238,130,66,26,194,98,247,255])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2656#usize 2688#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2656#usize 2688#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [126,121,251,104,220,255,47,155,0,110,75,75,75,176,125,193,113,66,44,179,9,60,208,17,238,130,66,26,194,98,247,255])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2656).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31015).take 32)=(encodeState (JGc_TX2_HashBytes.state [126,121,251,104,220,255,47,155,0,110,75,75,75,176,125,193,113,66,44,179,9,60,208,17,238,130,66,26,194,98,247,255])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2656#usize 2688#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [126,121,251,104,220,255,47,155,0,110,75,75,75,176,125,193,113,66,44,179,9,60,208,17,238,130,66,26,194,98,247,255])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [126,121,251,104,220,255,47,155,0,110,75,75,75,176,125,193,113,66,44,179,9,60,208,17,238,130,66,26,194,98,247,255]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [126,121,251,104,220,255,47,155,0,110,75,75,75,176,125,193,113,66,44,179,9,60,208,17,238,130,66,26,194,98,247,255])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2688#usize 2720#usize)=ok (encodeState (JGc_TX2_HashBytes.state [158,176,11,125,66,96,99,8,73,93,247,85,166,153,219,250,17,121,222,96,4,149,255,161,250,23,46,233,243,21,255,119])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2688#usize 2720#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2688#usize 2720#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [158,176,11,125,66,96,99,8,73,93,247,85,166,153,219,250,17,121,222,96,4,149,255,161,250,23,46,233,243,21,255,119])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2688).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31047).take 32)=(encodeState (JGc_TX2_HashBytes.state [158,176,11,125,66,96,99,8,73,93,247,85,166,153,219,250,17,121,222,96,4,149,255,161,250,23,46,233,243,21,255,119])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2688#usize 2720#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [158,176,11,125,66,96,99,8,73,93,247,85,166,153,219,250,17,121,222,96,4,149,255,161,250,23,46,233,243,21,255,119])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [158,176,11,125,66,96,99,8,73,93,247,85,166,153,219,250,17,121,222,96,4,149,255,161,250,23,46,233,243,21,255,119]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [158,176,11,125,66,96,99,8,73,93,247,85,166,153,219,250,17,121,222,96,4,149,255,161,250,23,46,233,243,21,255,119])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2720#usize 2752#usize)=ok (encodeState (JGc_TX2_HashBytes.state [207,177,176,60,127,81,118,135,169,148,236,21,219,140,173,74,233,123,232,214,172,56,152,55,156,176,4,122,1,49,209,83])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2720#usize 2752#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2720#usize 2752#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [207,177,176,60,127,81,118,135,169,148,236,21,219,140,173,74,233,123,232,214,172,56,152,55,156,176,4,122,1,49,209,83])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2720).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31079).take 32)=(encodeState (JGc_TX2_HashBytes.state [207,177,176,60,127,81,118,135,169,148,236,21,219,140,173,74,233,123,232,214,172,56,152,55,156,176,4,122,1,49,209,83])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2720#usize 2752#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [207,177,176,60,127,81,118,135,169,148,236,21,219,140,173,74,233,123,232,214,172,56,152,55,156,176,4,122,1,49,209,83])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [207,177,176,60,127,81,118,135,169,148,236,21,219,140,173,74,233,123,232,214,172,56,152,55,156,176,4,122,1,49,209,83]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [207,177,176,60,127,81,118,135,169,148,236,21,219,140,173,74,233,123,232,214,172,56,152,55,156,176,4,122,1,49,209,83])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2752#usize 2784#usize)=ok (encodeState (JGc_TX2_HashBytes.state [65,182,123,189,84,7,216,217,132,96,18,74,118,7,3,237,94,9,129,18,202,71,166,195,20,119,229,148,187,131,19,241])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2752#usize 2784#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2752#usize 2784#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [65,182,123,189,84,7,216,217,132,96,18,74,118,7,3,237,94,9,129,18,202,71,166,195,20,119,229,148,187,131,19,241])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2752).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31111).take 32)=(encodeState (JGc_TX2_HashBytes.state [65,182,123,189,84,7,216,217,132,96,18,74,118,7,3,237,94,9,129,18,202,71,166,195,20,119,229,148,187,131,19,241])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2752#usize 2784#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [65,182,123,189,84,7,216,217,132,96,18,74,118,7,3,237,94,9,129,18,202,71,166,195,20,119,229,148,187,131,19,241])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [65,182,123,189,84,7,216,217,132,96,18,74,118,7,3,237,94,9,129,18,202,71,166,195,20,119,229,148,187,131,19,241]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [65,182,123,189,84,7,216,217,132,96,18,74,118,7,3,237,94,9,129,18,202,71,166,195,20,119,229,148,187,131,19,241])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2784#usize 2816#usize)=ok (encodeState (JGc_TX2_HashBytes.state [151,189,242,15,48,2,126,127,42,140,208,198,249,228,165,254,222,43,136,1,116,49,161,30,227,32,117,1,201,85,56,26])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2784#usize 2816#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2784#usize 2816#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [151,189,242,15,48,2,126,127,42,140,208,198,249,228,165,254,222,43,136,1,116,49,161,30,227,32,117,1,201,85,56,26])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2784).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31143).take 32)=(encodeState (JGc_TX2_HashBytes.state [151,189,242,15,48,2,126,127,42,140,208,198,249,228,165,254,222,43,136,1,116,49,161,30,227,32,117,1,201,85,56,26])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2784#usize 2816#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [151,189,242,15,48,2,126,127,42,140,208,198,249,228,165,254,222,43,136,1,116,49,161,30,227,32,117,1,201,85,56,26])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [151,189,242,15,48,2,126,127,42,140,208,198,249,228,165,254,222,43,136,1,116,49,161,30,227,32,117,1,201,85,56,26]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [151,189,242,15,48,2,126,127,42,140,208,198,249,228,165,254,222,43,136,1,116,49,161,30,227,32,117,1,201,85,56,26])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2816#usize 2848#usize)=ok (encodeState (JGc_TX2_HashBytes.state [46,78,225,61,74,143,106,41,11,1,157,44,41,247,155,126,43,181,1,160,152,29,224,187,122,141,106,211,167,157,239,161])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2816#usize 2848#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2816#usize 2848#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [46,78,225,61,74,143,106,41,11,1,157,44,41,247,155,126,43,181,1,160,152,29,224,187,122,141,106,211,167,157,239,161])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2816).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31175).take 32)=(encodeState (JGc_TX2_HashBytes.state [46,78,225,61,74,143,106,41,11,1,157,44,41,247,155,126,43,181,1,160,152,29,224,187,122,141,106,211,167,157,239,161])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2816#usize 2848#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [46,78,225,61,74,143,106,41,11,1,157,44,41,247,155,126,43,181,1,160,152,29,224,187,122,141,106,211,167,157,239,161])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [46,78,225,61,74,143,106,41,11,1,157,44,41,247,155,126,43,181,1,160,152,29,224,187,122,141,106,211,167,157,239,161]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [46,78,225,61,74,143,106,41,11,1,157,44,41,247,155,126,43,181,1,160,152,29,224,187,122,141,106,211,167,157,239,161])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2848#usize 2880#usize)=ok (encodeState (JGc_TX2_HashBytes.state [8,249,218,86,52,33,101,166,203,237,91,36,157,221,19,10,53,117,89,94,91,68,66,227,193,115,151,105,136,220,126,108])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2848#usize 2880#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2848#usize 2880#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [8,249,218,86,52,33,101,166,203,237,91,36,157,221,19,10,53,117,89,94,91,68,66,227,193,115,151,105,136,220,126,108])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2848).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31207).take 32)=(encodeState (JGc_TX2_HashBytes.state [8,249,218,86,52,33,101,166,203,237,91,36,157,221,19,10,53,117,89,94,91,68,66,227,193,115,151,105,136,220,126,108])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2848#usize 2880#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [8,249,218,86,52,33,101,166,203,237,91,36,157,221,19,10,53,117,89,94,91,68,66,227,193,115,151,105,136,220,126,108])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [8,249,218,86,52,33,101,166,203,237,91,36,157,221,19,10,53,117,89,94,91,68,66,227,193,115,151,105,136,220,126,108]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [8,249,218,86,52,33,101,166,203,237,91,36,157,221,19,10,53,117,89,94,91,68,66,227,193,115,151,105,136,220,126,108])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 2560) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 2880 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 2560 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 256#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 2560 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value080) :=
    JGm_TX2_View.value (s00 s) indices00 values00 2560 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=2560#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠256#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨365#u32,JGm_TX2_View.index (s00 s) indices00 values00 2560 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s00 s).«at» 2592#usize)=ok (encodeState (JGc_TX2_HashBytes.state [113,23,49,153,65,62,50,121,121,134,77,85,4,221,172,58,119,143,25,248,30,111,211,227,9,191,95,71,39,81,225,50])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes0 0#usize 0#usize 1#usize 2592#usize 1856#usize
    256#u32 (encodeState value080) (encodeState (JGc_TX2_HashBytes.state [113,23,49,153,65,62,50,121,121,134,77,85,4,221,172,58,119,143,25,248,30,111,211,227,9,191,95,71,39,81,225,50])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read00
  simp only [show 256#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls0.source090 D hash (s00 s) 1#usize 2592#usize 256#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 2592 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 2560 v00
      256#u32 0#usize (encodeState value090) 2592#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 365#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 2592 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value081) :=
    JGm_TX2_View.value (s01 s) indices01 values01 2592 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=2592#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠365#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨576#u32,JGm_TX2_View.index (s01 s) indices01 values01 2592 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s01 s).«at» 2624#usize)=ok (encodeState (JGc_TX2_HashBytes.state [17,86,79,88,53,63,109,64,216,191,11,30,55,109,89,48,69,42,142,22,51,233,130,145,169,63,100,38,75,249,74,19])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes0 1#usize 1#usize 2#usize 2624#usize 1824#usize
    365#u32 (encodeState value081) (encodeState (JGc_TX2_HashBytes.state [17,86,79,88,53,63,109,64,216,191,11,30,55,109,89,48,69,42,142,22,51,233,130,145,169,63,100,38,75,249,74,19])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read01
  simp only [show 365#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes0 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls0.source091 D hash (s01 s) 2#usize 2624#usize 365#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 2624 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 2592 v01
      365#u32 1#usize (encodeState value091) 2624#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 576#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 2624 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value082) :=
    JGm_TX2_View.value (s02 s) indices02 values02 2624 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=2624#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠576#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨624#u32,JGm_TX2_View.index (s02 s) indices02 values02 2624 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s02 s).«at» 2656#usize)=ok (encodeState (JGc_TX2_HashBytes.state [226,155,182,235,137,88,156,193,14,203,121,8,103,202,235,239,155,117,229,172,214,169,41,35,14,166,228,96,191,226,79,63])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes0 2#usize 2#usize 3#usize 2656#usize 1792#usize
    576#u32 (encodeState value082) (encodeState (JGc_TX2_HashBytes.state [226,155,182,235,137,88,156,193,14,203,121,8,103,202,235,239,155,117,229,172,214,169,41,35,14,166,228,96,191,226,79,63])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read02
  simp only [show 576#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes0 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls0.source092 D hash (s02 s) 3#usize 2656#usize 576#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 2656 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 2624 v02
      576#u32 2#usize (encodeState value092) 2656#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 624#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 2656 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value083) :=
    JGm_TX2_View.value (s03 s) indices03 values03 2656 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=2656#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠624#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨718#u32,JGm_TX2_View.index (s03 s) indices03 values03 2656 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s03 s).«at» 2688#usize)=ok (encodeState (JGc_TX2_HashBytes.state [126,121,251,104,220,255,47,155,0,110,75,75,75,176,125,193,113,66,44,179,9,60,208,17,238,130,66,26,194,98,247,255])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes0 3#usize 3#usize 4#usize 2688#usize 1760#usize
    624#u32 (encodeState value083) (encodeState (JGc_TX2_HashBytes.state [126,121,251,104,220,255,47,155,0,110,75,75,75,176,125,193,113,66,44,179,9,60,208,17,238,130,66,26,194,98,247,255])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read03
  simp only [show 624#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes0 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls0.source093 D hash (s03 s) 4#usize 2688#usize 624#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 2688 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 2656 v03
      624#u32 3#usize (encodeState value093) 2688#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 718#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 2688 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value084) :=
    JGm_TX2_View.value (s04 s) indices04 values04 2688 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=2688#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠718#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨751#u32,JGm_TX2_View.index (s04 s) indices04 values04 2688 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s04 s).«at» 2720#usize)=ok (encodeState (JGc_TX2_HashBytes.state [158,176,11,125,66,96,99,8,73,93,247,85,166,153,219,250,17,121,222,96,4,149,255,161,250,23,46,233,243,21,255,119])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes0 4#usize 4#usize 5#usize 2720#usize 1728#usize
    718#u32 (encodeState value084) (encodeState (JGc_TX2_HashBytes.state [158,176,11,125,66,96,99,8,73,93,247,85,166,153,219,250,17,121,222,96,4,149,255,161,250,23,46,233,243,21,255,119])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read04
  simp only [show 718#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes0 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls0.source094 D hash (s04 s) 5#usize 2720#usize 718#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 2720 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 2688 v04
      718#u32 4#usize (encodeState value094) 2720#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 751#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 2720 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value085) :=
    JGm_TX2_View.value (s05 s) indices05 values05 2720 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=2720#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠751#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨754#u32,JGm_TX2_View.index (s05 s) indices05 values05 2720 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s05 s).«at» 2752#usize)=ok (encodeState (JGc_TX2_HashBytes.state [207,177,176,60,127,81,118,135,169,148,236,21,219,140,173,74,233,123,232,214,172,56,152,55,156,176,4,122,1,49,209,83])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes0 5#usize 5#usize 6#usize 2752#usize 1696#usize
    751#u32 (encodeState value085) (encodeState (JGc_TX2_HashBytes.state [207,177,176,60,127,81,118,135,169,148,236,21,219,140,173,74,233,123,232,214,172,56,152,55,156,176,4,122,1,49,209,83])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read05
  simp only [show 751#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes0 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls0.source095 D hash (s05 s) 6#usize 2752#usize 751#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 2752 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 2720 v05
      751#u32 5#usize (encodeState value095) 2752#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 754#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 2752 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value086) :=
    JGm_TX2_View.value (s06 s) indices06 values06 2752 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=2752#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠754#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨817#u32,JGm_TX2_View.index (s06 s) indices06 values06 2752 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s06 s).«at» 2784#usize)=ok (encodeState (JGc_TX2_HashBytes.state [65,182,123,189,84,7,216,217,132,96,18,74,118,7,3,237,94,9,129,18,202,71,166,195,20,119,229,148,187,131,19,241])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes0 6#usize 6#usize 7#usize 2784#usize 1664#usize
    754#u32 (encodeState value086) (encodeState (JGc_TX2_HashBytes.state [65,182,123,189,84,7,216,217,132,96,18,74,118,7,3,237,94,9,129,18,202,71,166,195,20,119,229,148,187,131,19,241])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read06
  simp only [show 754#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes0 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls0.source096 D hash (s06 s) 7#usize 2784#usize 754#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 2784 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 2752 v06
      754#u32 6#usize (encodeState value096) 2784#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 817#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 2784 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value087) :=
    JGm_TX2_View.value (s07 s) indices07 values07 2784 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=2784#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠817#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨846#u32,JGm_TX2_View.index (s07 s) indices07 values07 2784 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s07 s).«at» 2816#usize)=ok (encodeState (JGc_TX2_HashBytes.state [151,189,242,15,48,2,126,127,42,140,208,198,249,228,165,254,222,43,136,1,116,49,161,30,227,32,117,1,201,85,56,26])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes0 7#usize 7#usize 8#usize 2816#usize 1632#usize
    817#u32 (encodeState value087) (encodeState (JGc_TX2_HashBytes.state [151,189,242,15,48,2,126,127,42,140,208,198,249,228,165,254,222,43,136,1,116,49,161,30,227,32,117,1,201,85,56,26])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read07
  simp only [show 817#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes0 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls0.source097 D hash (s07 s) 8#usize 2816#usize 817#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 2816 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 2784 v07
      817#u32 7#usize (encodeState value097) 2816#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 846#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 2816 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value088) :=
    JGm_TX2_View.value (s08 s) indices08 values08 2816 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=2816#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠846#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨960#u32,JGm_TX2_View.index (s08 s) indices08 values08 2816 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s08 s).«at» 2848#usize)=ok (encodeState (JGc_TX2_HashBytes.state [46,78,225,61,74,143,106,41,11,1,157,44,41,247,155,126,43,181,1,160,152,29,224,187,122,141,106,211,167,157,239,161])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes0 8#usize 8#usize 9#usize 2848#usize 1600#usize
    846#u32 (encodeState value088) (encodeState (JGc_TX2_HashBytes.state [46,78,225,61,74,143,106,41,11,1,157,44,41,247,155,126,43,181,1,160,152,29,224,187,122,141,106,211,167,157,239,161])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read08
  simp only [show 846#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes0 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls0.source098 D hash (s08 s) 9#usize 2848#usize 846#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 2848 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 2816 v08
      846#u32 8#usize (encodeState value098) 2848#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 960#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 2848 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value089) :=
    JGm_TX2_View.value (s09 s) indices09 values09 2848 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=2848#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠960#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s09 s).«at» 2880#usize)=ok (encodeState (JGc_TX2_HashBytes.state [8,249,218,86,52,33,101,166,203,237,91,36,157,221,19,10,53,117,89,94,91,68,66,227,193,115,151,105,136,220,126,108])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes0 9#usize 9#usize 10#usize 2880#usize 1568#usize
    960#u32 (encodeState value089) (encodeState (JGc_TX2_HashBytes.state [8,249,218,86,52,33,101,166,203,237,91,36,157,221,19,10,53,117,89,94,91,68,66,227,193,115,151,105,136,220,126,108])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read09
  simp only [show 960#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes0 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls0.source099 D hash (s09 s) 10#usize 2880#usize 960#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 2880 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 2848 v09
      960#u32 9#usize (encodeState value099) 2880#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes0 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes0 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes0 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes0 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes0 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes0 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes0 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes0 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes0 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes0 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes0 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 2880
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level0_08
end


end
