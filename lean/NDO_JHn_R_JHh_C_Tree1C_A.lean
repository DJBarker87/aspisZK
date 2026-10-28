import RPt_JFq_Range
import NDO_JFw_Frames
import JGm_TX2_HeightTools
import NDO_JGm_TX2_View
import NDO_JGy_LightCore
import NDO_JGy_LightPadding
import NDO_JHn_R_JHh_C_Tree1B
import NDO_JHe_SHARealization
import JHn_R_JHh_SmallConstants
section
variable [sha : AspisR1.JHe_SHARealization]
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_06
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
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
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1920#usize 1952#usize)=ok (encodeState (JGc_TX2_HashBytes.state [213,219,66,149,132,102,202,223,2,186,92,70,102,98,174,29,190,20,146,248,36,151,27,124,170,129,132,58,230,86,6,226])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1920#usize 1952#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1920#usize 1952#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [213,219,66,149,132,102,202,223,2,186,92,70,102,98,174,29,190,20,146,248,36,151,27,124,170,129,132,58,230,86,6,226])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1920).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34951).take 32)=(encodeState (JGc_TX2_HashBytes.state [213,219,66,149,132,102,202,223,2,186,92,70,102,98,174,29,190,20,146,248,36,151,27,124,170,129,132,58,230,86,6,226])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1920#usize 1952#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [213,219,66,149,132,102,202,223,2,186,92,70,102,98,174,29,190,20,146,248,36,151,27,124,170,129,132,58,230,86,6,226])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [213,219,66,149,132,102,202,223,2,186,92,70,102,98,174,29,190,20,146,248,36,151,27,124,170,129,132,58,230,86,6,226]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [213,219,66,149,132,102,202,223,2,186,92,70,102,98,174,29,190,20,146,248,36,151,27,124,170,129,132,58,230,86,6,226])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1952#usize 1984#usize)=ok (encodeState (JGc_TX2_HashBytes.state [43,41,156,176,42,40,47,242,5,243,149,73,246,84,151,201,214,4,0,213,156,115,60,243,26,35,74,120,199,7,124,249])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1952#usize 1984#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1952#usize 1984#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [43,41,156,176,42,40,47,242,5,243,149,73,246,84,151,201,214,4,0,213,156,115,60,243,26,35,74,120,199,7,124,249])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1952).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34983).take 32)=(encodeState (JGc_TX2_HashBytes.state [43,41,156,176,42,40,47,242,5,243,149,73,246,84,151,201,214,4,0,213,156,115,60,243,26,35,74,120,199,7,124,249])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1952#usize 1984#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [43,41,156,176,42,40,47,242,5,243,149,73,246,84,151,201,214,4,0,213,156,115,60,243,26,35,74,120,199,7,124,249])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [43,41,156,176,42,40,47,242,5,243,149,73,246,84,151,201,214,4,0,213,156,115,60,243,26,35,74,120,199,7,124,249]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [43,41,156,176,42,40,47,242,5,243,149,73,246,84,151,201,214,4,0,213,156,115,60,243,26,35,74,120,199,7,124,249])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1984#usize 2016#usize)=ok (encodeState (JGc_TX2_HashBytes.state [166,169,50,209,188,5,52,23,33,230,174,188,64,116,191,107,219,82,103,128,10,79,137,212,138,189,23,60,71,204,95,45])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1984#usize 2016#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1984#usize 2016#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [166,169,50,209,188,5,52,23,33,230,174,188,64,116,191,107,219,82,103,128,10,79,137,212,138,189,23,60,71,204,95,45])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1984).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35015).take 32)=(encodeState (JGc_TX2_HashBytes.state [166,169,50,209,188,5,52,23,33,230,174,188,64,116,191,107,219,82,103,128,10,79,137,212,138,189,23,60,71,204,95,45])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1984#usize 2016#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [166,169,50,209,188,5,52,23,33,230,174,188,64,116,191,107,219,82,103,128,10,79,137,212,138,189,23,60,71,204,95,45])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [166,169,50,209,188,5,52,23,33,230,174,188,64,116,191,107,219,82,103,128,10,79,137,212,138,189,23,60,71,204,95,45]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [166,169,50,209,188,5,52,23,33,230,174,188,64,116,191,107,219,82,103,128,10,79,137,212,138,189,23,60,71,204,95,45])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2016#usize 2048#usize)=ok (encodeState (JGc_TX2_HashBytes.state [26,45,196,149,156,185,207,108,35,63,83,156,140,215,142,227,222,78,13,88,119,76,111,150,75,170,136,157,17,249,95,75])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2016#usize 2048#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2016#usize 2048#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [26,45,196,149,156,185,207,108,35,63,83,156,140,215,142,227,222,78,13,88,119,76,111,150,75,170,136,157,17,249,95,75])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2016).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35047).take 32)=(encodeState (JGc_TX2_HashBytes.state [26,45,196,149,156,185,207,108,35,63,83,156,140,215,142,227,222,78,13,88,119,76,111,150,75,170,136,157,17,249,95,75])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2016#usize 2048#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [26,45,196,149,156,185,207,108,35,63,83,156,140,215,142,227,222,78,13,88,119,76,111,150,75,170,136,157,17,249,95,75])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [26,45,196,149,156,185,207,108,35,63,83,156,140,215,142,227,222,78,13,88,119,76,111,150,75,170,136,157,17,249,95,75]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [26,45,196,149,156,185,207,108,35,63,83,156,140,215,142,227,222,78,13,88,119,76,111,150,75,170,136,157,17,249,95,75])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2048#usize 2080#usize)=ok (encodeState (JGc_TX2_HashBytes.state [187,168,249,177,7,164,3,149,98,161,102,174,50,138,206,11,30,72,150,177,137,51,106,119,176,70,87,242,152,194,189,85])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2048#usize 2080#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2048#usize 2080#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [187,168,249,177,7,164,3,149,98,161,102,174,50,138,206,11,30,72,150,177,137,51,106,119,176,70,87,242,152,194,189,85])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2048).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35079).take 32)=(encodeState (JGc_TX2_HashBytes.state [187,168,249,177,7,164,3,149,98,161,102,174,50,138,206,11,30,72,150,177,137,51,106,119,176,70,87,242,152,194,189,85])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2048#usize 2080#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [187,168,249,177,7,164,3,149,98,161,102,174,50,138,206,11,30,72,150,177,137,51,106,119,176,70,87,242,152,194,189,85])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [187,168,249,177,7,164,3,149,98,161,102,174,50,138,206,11,30,72,150,177,137,51,106,119,176,70,87,242,152,194,189,85]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [187,168,249,177,7,164,3,149,98,161,102,174,50,138,206,11,30,72,150,177,137,51,106,119,176,70,87,242,152,194,189,85])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2080#usize 2112#usize)=ok (encodeState (JGc_TX2_HashBytes.state [73,221,130,144,71,67,136,79,167,63,161,205,39,10,20,47,38,23,24,180,153,220,23,255,9,108,57,158,87,153,49,94])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2080#usize 2112#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2080#usize 2112#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [73,221,130,144,71,67,136,79,167,63,161,205,39,10,20,47,38,23,24,180,153,220,23,255,9,108,57,158,87,153,49,94])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2080).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35111).take 32)=(encodeState (JGc_TX2_HashBytes.state [73,221,130,144,71,67,136,79,167,63,161,205,39,10,20,47,38,23,24,180,153,220,23,255,9,108,57,158,87,153,49,94])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2080#usize 2112#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [73,221,130,144,71,67,136,79,167,63,161,205,39,10,20,47,38,23,24,180,153,220,23,255,9,108,57,158,87,153,49,94])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [73,221,130,144,71,67,136,79,167,63,161,205,39,10,20,47,38,23,24,180,153,220,23,255,9,108,57,158,87,153,49,94]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [73,221,130,144,71,67,136,79,167,63,161,205,39,10,20,47,38,23,24,180,153,220,23,255,9,108,57,158,87,153,49,94])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2112#usize 2144#usize)=ok (encodeState (JGc_TX2_HashBytes.state [167,255,250,78,90,35,106,202,120,194,253,220,221,11,157,53,242,35,22,107,23,89,62,195,225,140,7,190,221,244,119,208])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2112#usize 2144#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2112#usize 2144#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [167,255,250,78,90,35,106,202,120,194,253,220,221,11,157,53,242,35,22,107,23,89,62,195,225,140,7,190,221,244,119,208])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2112).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35143).take 32)=(encodeState (JGc_TX2_HashBytes.state [167,255,250,78,90,35,106,202,120,194,253,220,221,11,157,53,242,35,22,107,23,89,62,195,225,140,7,190,221,244,119,208])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2112#usize 2144#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [167,255,250,78,90,35,106,202,120,194,253,220,221,11,157,53,242,35,22,107,23,89,62,195,225,140,7,190,221,244,119,208])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [167,255,250,78,90,35,106,202,120,194,253,220,221,11,157,53,242,35,22,107,23,89,62,195,225,140,7,190,221,244,119,208]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [167,255,250,78,90,35,106,202,120,194,253,220,221,11,157,53,242,35,22,107,23,89,62,195,225,140,7,190,221,244,119,208])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2144#usize 2176#usize)=ok (encodeState (JGc_TX2_HashBytes.state [214,112,195,229,164,168,187,90,35,77,255,198,103,221,16,135,157,106,196,94,83,69,143,19,82,171,67,25,74,114,34,81])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2144#usize 2176#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2144#usize 2176#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [214,112,195,229,164,168,187,90,35,77,255,198,103,221,16,135,157,106,196,94,83,69,143,19,82,171,67,25,74,114,34,81])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2144).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35175).take 32)=(encodeState (JGc_TX2_HashBytes.state [214,112,195,229,164,168,187,90,35,77,255,198,103,221,16,135,157,106,196,94,83,69,143,19,82,171,67,25,74,114,34,81])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2144#usize 2176#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [214,112,195,229,164,168,187,90,35,77,255,198,103,221,16,135,157,106,196,94,83,69,143,19,82,171,67,25,74,114,34,81])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [214,112,195,229,164,168,187,90,35,77,255,198,103,221,16,135,157,106,196,94,83,69,143,19,82,171,67,25,74,114,34,81]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [214,112,195,229,164,168,187,90,35,77,255,198,103,221,16,135,157,106,196,94,83,69,143,19,82,171,67,25,74,114,34,81])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2176#usize 2208#usize)=ok (encodeState (JGc_TX2_HashBytes.state [99,164,177,65,229,155,166,198,59,58,144,40,119,57,191,57,32,230,224,109,132,52,196,152,102,228,8,147,143,111,177,238])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2176#usize 2208#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2176#usize 2208#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [99,164,177,65,229,155,166,198,59,58,144,40,119,57,191,57,32,230,224,109,132,52,196,152,102,228,8,147,143,111,177,238])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2176).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35207).take 32)=(encodeState (JGc_TX2_HashBytes.state [99,164,177,65,229,155,166,198,59,58,144,40,119,57,191,57,32,230,224,109,132,52,196,152,102,228,8,147,143,111,177,238])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2176#usize 2208#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [99,164,177,65,229,155,166,198,59,58,144,40,119,57,191,57,32,230,224,109,132,52,196,152,102,228,8,147,143,111,177,238])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [99,164,177,65,229,155,166,198,59,58,144,40,119,57,191,57,32,230,224,109,132,52,196,152,102,228,8,147,143,111,177,238]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [99,164,177,65,229,155,166,198,59,58,144,40,119,57,191,57,32,230,224,109,132,52,196,152,102,228,8,147,143,111,177,238])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2208#usize 2240#usize)=ok (encodeState (JGc_TX2_HashBytes.state [206,137,116,72,150,225,247,109,190,174,193,175,97,74,39,239,82,242,9,20,245,218,106,203,31,54,175,142,188,88,174,158])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2208#usize 2240#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2208#usize 2240#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [206,137,116,72,150,225,247,109,190,174,193,175,97,74,39,239,82,242,9,20,245,218,106,203,31,54,175,142,188,88,174,158])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2208).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35239).take 32)=(encodeState (JGc_TX2_HashBytes.state [206,137,116,72,150,225,247,109,190,174,193,175,97,74,39,239,82,242,9,20,245,218,106,203,31,54,175,142,188,88,174,158])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2208#usize 2240#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [206,137,116,72,150,225,247,109,190,174,193,175,97,74,39,239,82,242,9,20,245,218,106,203,31,54,175,142,188,88,174,158])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [206,137,116,72,150,225,247,109,190,174,193,175,97,74,39,239,82,242,9,20,245,218,106,203,31,54,175,142,188,88,174,158]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [206,137,116,72,150,225,247,109,190,174,193,175,97,74,39,239,82,242,9,20,245,218,106,203,31,54,175,142,188,88,174,158])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 1920) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
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
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 1952#usize)=ok (encodeState (JGc_TX2_HashBytes.state [213,219,66,149,132,102,202,223,2,186,92,70,102,98,174,29,190,20,146,248,36,151,27,124,170,129,132,58,230,86,6,226])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 1952#usize 2496#usize
    1024#u32 (encodeState value060) (encodeState (JGc_TX2_HashBytes.state [213,219,66,149,132,102,202,223,2,186,92,70,102,98,174,29,190,20,146,248,36,151,27,124,170,129,132,58,230,86,6,226])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 1024#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source070 D hash (s00 s) 1#usize 1952#usize 1024#u32 0#usize (by decide)
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
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 1984#usize)=ok (encodeState (JGc_TX2_HashBytes.state [43,41,156,176,42,40,47,242,5,243,149,73,246,84,151,201,214,4,0,213,156,115,60,243,26,35,74,120,199,7,124,249])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 1984#usize 2464#usize
    1460#u32 (encodeState value061) (encodeState (JGc_TX2_HashBytes.state [43,41,156,176,42,40,47,242,5,243,149,73,246,84,151,201,214,4,0,213,156,115,60,243,26,35,74,120,199,7,124,249])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 1460#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source071 D hash (s01 s) 2#usize 1984#usize 1460#u32 1#usize (by decide)
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
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s02 s).«at» 2016#usize)=ok (encodeState (JGc_TX2_HashBytes.state [166,169,50,209,188,5,52,23,33,230,174,188,64,116,191,107,219,82,103,128,10,79,137,212,138,189,23,60,71,204,95,45])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 2#usize 3#usize 2016#usize 2432#usize
    2305#u32 (encodeState value062) (encodeState (JGc_TX2_HashBytes.state [166,169,50,209,188,5,52,23,33,230,174,188,64,116,191,107,219,82,103,128,10,79,137,212,138,189,23,60,71,204,95,45])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read02
  simp only [show 2305#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls1.source072 D hash (s02 s) 3#usize 2016#usize 2305#u32 2#usize (by decide)
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
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s03 s).«at» 2048#usize)=ok (encodeState (JGc_TX2_HashBytes.state [26,45,196,149,156,185,207,108,35,63,83,156,140,215,142,227,222,78,13,88,119,76,111,150,75,170,136,157,17,249,95,75])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 3#usize 4#usize 2048#usize 2400#usize
    2497#u32 (encodeState value063) (encodeState (JGc_TX2_HashBytes.state [26,45,196,149,156,185,207,108,35,63,83,156,140,215,142,227,222,78,13,88,119,76,111,150,75,170,136,157,17,249,95,75])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read03
  simp only [show 2497#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls1.source073 D hash (s03 s) 4#usize 2048#usize 2497#u32 3#usize (by decide)
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
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 2080#usize)=ok (encodeState (JGc_TX2_HashBytes.state [187,168,249,177,7,164,3,149,98,161,102,174,50,138,206,11,30,72,150,177,137,51,106,119,176,70,87,242,152,194,189,85])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 4#usize 5#usize 2080#usize 2368#usize
    2872#u32 (encodeState value064) (encodeState (JGc_TX2_HashBytes.state [187,168,249,177,7,164,3,149,98,161,102,174,50,138,206,11,30,72,150,177,137,51,106,119,176,70,87,242,152,194,189,85])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 2872#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source074 D hash (s04 s) 5#usize 2080#usize 2872#u32 4#usize (by decide)
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
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s05 s).«at» 2112#usize)=ok (encodeState (JGc_TX2_HashBytes.state [73,221,130,144,71,67,136,79,167,63,161,205,39,10,20,47,38,23,24,180,153,220,23,255,9,108,57,158,87,153,49,94])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes1 5#usize 5#usize 6#usize 2112#usize 2336#usize
    3004#u32 (encodeState value065) (encodeState (JGc_TX2_HashBytes.state [73,221,130,144,71,67,136,79,167,63,161,205,39,10,20,47,38,23,24,180,153,220,23,255,9,108,57,158,87,153,49,94])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read05
  simp only [show 3004#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls1.source075 D hash (s05 s) 6#usize 2112#usize 3004#u32 5#usize (by decide)
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
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s06 s).«at» 2144#usize)=ok (encodeState (JGc_TX2_HashBytes.state [167,255,250,78,90,35,106,202,120,194,253,220,221,11,157,53,242,35,22,107,23,89,62,195,225,140,7,190,221,244,119,208])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes1 6#usize 6#usize 7#usize 2144#usize 2304#usize
    3017#u32 (encodeState value066) (encodeState (JGc_TX2_HashBytes.state [167,255,250,78,90,35,106,202,120,194,253,220,221,11,157,53,242,35,22,107,23,89,62,195,225,140,7,190,221,244,119,208])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read06
  simp only [show 3017#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls1.source076 D hash (s06 s) 7#usize 2144#usize 3017#u32 6#usize (by decide)
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
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s07 s).«at» 2176#usize)=ok (encodeState (JGc_TX2_HashBytes.state [214,112,195,229,164,168,187,90,35,77,255,198,103,221,16,135,157,106,196,94,83,69,143,19,82,171,67,25,74,114,34,81])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes1 7#usize 7#usize 8#usize 2176#usize 2272#usize
    3271#u32 (encodeState value067) (encodeState (JGc_TX2_HashBytes.state [214,112,195,229,164,168,187,90,35,77,255,198,103,221,16,135,157,106,196,94,83,69,143,19,82,171,67,25,74,114,34,81])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read07
  simp only [show 3271#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls1.source077 D hash (s07 s) 8#usize 2176#usize 3271#u32 7#usize (by decide)
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
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s08 s).«at» 2208#usize)=ok (encodeState (JGc_TX2_HashBytes.state [99,164,177,65,229,155,166,198,59,58,144,40,119,57,191,57,32,230,224,109,132,52,196,152,102,228,8,147,143,111,177,238])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes1 8#usize 8#usize 9#usize 2208#usize 2240#usize
    3387#u32 (encodeState value068) (encodeState (JGc_TX2_HashBytes.state [99,164,177,65,229,155,166,198,59,58,144,40,119,57,191,57,32,230,224,109,132,52,196,152,102,228,8,147,143,111,177,238])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read08
  simp only [show 3387#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls1.source078 D hash (s08 s) 9#usize 2208#usize 3387#u32 8#usize (by decide)
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
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s09 s).«at» 2240#usize)=ok (encodeState (JGc_TX2_HashBytes.state [206,137,116,72,150,225,247,109,190,174,193,175,97,74,39,239,82,242,9,20,245,218,106,203,31,54,175,142,188,88,174,158])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes1 9#usize 9#usize 10#usize 2240#usize 2208#usize
    3842#u32 (encodeState value069) (encodeState (JGc_TX2_HashBytes.state [206,137,116,72,150,225,247,109,190,174,193,175,97,74,39,239,82,242,9,20,245,218,106,203,31,54,175,142,188,88,174,158])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read09
  simp only [show 3842#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls1.source079 D hash (s09 s) 10#usize 2240#usize 3842#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 2240 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 2208 v09
      3842#u32 9#usize (encodeState value079) 2240#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes1 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 2240
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_06
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_07
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
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
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2240#usize 2272#usize)=ok (encodeState (JGc_TX2_HashBytes.state [86,144,167,147,188,24,122,130,134,42,53,1,191,205,208,232,136,53,92,205,132,56,195,95,102,211,36,136,20,102,109,234])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2240#usize 2272#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2240#usize 2272#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [86,144,167,147,188,24,122,130,134,42,53,1,191,205,208,232,136,53,92,205,132,56,195,95,102,211,36,136,20,102,109,234])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2240).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35271).take 32)=(encodeState (JGc_TX2_HashBytes.state [86,144,167,147,188,24,122,130,134,42,53,1,191,205,208,232,136,53,92,205,132,56,195,95,102,211,36,136,20,102,109,234])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2240#usize 2272#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [86,144,167,147,188,24,122,130,134,42,53,1,191,205,208,232,136,53,92,205,132,56,195,95,102,211,36,136,20,102,109,234])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [86,144,167,147,188,24,122,130,134,42,53,1,191,205,208,232,136,53,92,205,132,56,195,95,102,211,36,136,20,102,109,234]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [86,144,167,147,188,24,122,130,134,42,53,1,191,205,208,232,136,53,92,205,132,56,195,95,102,211,36,136,20,102,109,234])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2272#usize 2304#usize)=ok (encodeState (JGc_TX2_HashBytes.state [129,134,159,111,208,119,101,44,121,214,241,176,100,83,224,186,157,157,52,15,168,151,4,234,77,57,92,217,53,20,243,178])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2272#usize 2304#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2272#usize 2304#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [129,134,159,111,208,119,101,44,121,214,241,176,100,83,224,186,157,157,52,15,168,151,4,234,77,57,92,217,53,20,243,178])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2272).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35303).take 32)=(encodeState (JGc_TX2_HashBytes.state [129,134,159,111,208,119,101,44,121,214,241,176,100,83,224,186,157,157,52,15,168,151,4,234,77,57,92,217,53,20,243,178])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2272#usize 2304#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [129,134,159,111,208,119,101,44,121,214,241,176,100,83,224,186,157,157,52,15,168,151,4,234,77,57,92,217,53,20,243,178])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [129,134,159,111,208,119,101,44,121,214,241,176,100,83,224,186,157,157,52,15,168,151,4,234,77,57,92,217,53,20,243,178]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [129,134,159,111,208,119,101,44,121,214,241,176,100,83,224,186,157,157,52,15,168,151,4,234,77,57,92,217,53,20,243,178])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2304#usize 2336#usize)=ok (encodeState (JGc_TX2_HashBytes.state [229,14,215,228,251,27,121,138,26,111,165,216,200,216,201,136,85,212,71,42,31,194,225,192,175,105,184,67,0,188,222,153])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2304#usize 2336#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2304#usize 2336#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [229,14,215,228,251,27,121,138,26,111,165,216,200,216,201,136,85,212,71,42,31,194,225,192,175,105,184,67,0,188,222,153])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2304).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35335).take 32)=(encodeState (JGc_TX2_HashBytes.state [229,14,215,228,251,27,121,138,26,111,165,216,200,216,201,136,85,212,71,42,31,194,225,192,175,105,184,67,0,188,222,153])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2304#usize 2336#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [229,14,215,228,251,27,121,138,26,111,165,216,200,216,201,136,85,212,71,42,31,194,225,192,175,105,184,67,0,188,222,153])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [229,14,215,228,251,27,121,138,26,111,165,216,200,216,201,136,85,212,71,42,31,194,225,192,175,105,184,67,0,188,222,153]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [229,14,215,228,251,27,121,138,26,111,165,216,200,216,201,136,85,212,71,42,31,194,225,192,175,105,184,67,0,188,222,153])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2336#usize 2368#usize)=ok (encodeState (JGc_TX2_HashBytes.state [46,123,57,164,118,22,77,38,72,105,83,9,179,113,17,42,45,247,143,151,243,173,174,143,222,205,203,31,224,130,255,177])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2336#usize 2368#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2336#usize 2368#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [46,123,57,164,118,22,77,38,72,105,83,9,179,113,17,42,45,247,143,151,243,173,174,143,222,205,203,31,224,130,255,177])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2336).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35367).take 32)=(encodeState (JGc_TX2_HashBytes.state [46,123,57,164,118,22,77,38,72,105,83,9,179,113,17,42,45,247,143,151,243,173,174,143,222,205,203,31,224,130,255,177])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2336#usize 2368#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [46,123,57,164,118,22,77,38,72,105,83,9,179,113,17,42,45,247,143,151,243,173,174,143,222,205,203,31,224,130,255,177])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [46,123,57,164,118,22,77,38,72,105,83,9,179,113,17,42,45,247,143,151,243,173,174,143,222,205,203,31,224,130,255,177]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [46,123,57,164,118,22,77,38,72,105,83,9,179,113,17,42,45,247,143,151,243,173,174,143,222,205,203,31,224,130,255,177])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2368#usize 2400#usize)=ok (encodeState (JGc_TX2_HashBytes.state [20,207,22,9,174,31,23,223,78,200,11,111,211,240,97,165,212,117,32,89,62,177,230,187,171,248,29,209,77,89,205,216])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2368#usize 2400#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2368#usize 2400#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [20,207,22,9,174,31,23,223,78,200,11,111,211,240,97,165,212,117,32,89,62,177,230,187,171,248,29,209,77,89,205,216])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2368).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35399).take 32)=(encodeState (JGc_TX2_HashBytes.state [20,207,22,9,174,31,23,223,78,200,11,111,211,240,97,165,212,117,32,89,62,177,230,187,171,248,29,209,77,89,205,216])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2368#usize 2400#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [20,207,22,9,174,31,23,223,78,200,11,111,211,240,97,165,212,117,32,89,62,177,230,187,171,248,29,209,77,89,205,216])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [20,207,22,9,174,31,23,223,78,200,11,111,211,240,97,165,212,117,32,89,62,177,230,187,171,248,29,209,77,89,205,216]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [20,207,22,9,174,31,23,223,78,200,11,111,211,240,97,165,212,117,32,89,62,177,230,187,171,248,29,209,77,89,205,216])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2400#usize 2432#usize)=ok (encodeState (JGc_TX2_HashBytes.state [152,7,48,143,226,24,235,182,175,169,50,91,216,225,126,157,236,234,179,168,64,123,15,245,94,142,196,215,212,12,175,250])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2400#usize 2432#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2400#usize 2432#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [152,7,48,143,226,24,235,182,175,169,50,91,216,225,126,157,236,234,179,168,64,123,15,245,94,142,196,215,212,12,175,250])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2400).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35431).take 32)=(encodeState (JGc_TX2_HashBytes.state [152,7,48,143,226,24,235,182,175,169,50,91,216,225,126,157,236,234,179,168,64,123,15,245,94,142,196,215,212,12,175,250])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2400#usize 2432#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [152,7,48,143,226,24,235,182,175,169,50,91,216,225,126,157,236,234,179,168,64,123,15,245,94,142,196,215,212,12,175,250])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [152,7,48,143,226,24,235,182,175,169,50,91,216,225,126,157,236,234,179,168,64,123,15,245,94,142,196,215,212,12,175,250]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [152,7,48,143,226,24,235,182,175,169,50,91,216,225,126,157,236,234,179,168,64,123,15,245,94,142,196,215,212,12,175,250])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2432#usize 2464#usize)=ok (encodeState (JGc_TX2_HashBytes.state [152,67,185,114,180,230,228,197,92,49,68,3,243,160,35,107,236,112,86,221,8,66,205,238,116,218,35,5,165,164,99,104])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2432#usize 2464#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2432#usize 2464#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [152,67,185,114,180,230,228,197,92,49,68,3,243,160,35,107,236,112,86,221,8,66,205,238,116,218,35,5,165,164,99,104])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2432).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35463).take 32)=(encodeState (JGc_TX2_HashBytes.state [152,67,185,114,180,230,228,197,92,49,68,3,243,160,35,107,236,112,86,221,8,66,205,238,116,218,35,5,165,164,99,104])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2432#usize 2464#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [152,67,185,114,180,230,228,197,92,49,68,3,243,160,35,107,236,112,86,221,8,66,205,238,116,218,35,5,165,164,99,104])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [152,67,185,114,180,230,228,197,92,49,68,3,243,160,35,107,236,112,86,221,8,66,205,238,116,218,35,5,165,164,99,104]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [152,67,185,114,180,230,228,197,92,49,68,3,243,160,35,107,236,112,86,221,8,66,205,238,116,218,35,5,165,164,99,104])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2464#usize 2496#usize)=ok (encodeState (JGc_TX2_HashBytes.state [121,222,231,1,61,67,70,17,115,85,96,65,234,200,241,83,60,16,185,45,192,179,155,106,241,106,46,40,153,49,208,171])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2464#usize 2496#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2464#usize 2496#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [121,222,231,1,61,67,70,17,115,85,96,65,234,200,241,83,60,16,185,45,192,179,155,106,241,106,46,40,153,49,208,171])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2464).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35495).take 32)=(encodeState (JGc_TX2_HashBytes.state [121,222,231,1,61,67,70,17,115,85,96,65,234,200,241,83,60,16,185,45,192,179,155,106,241,106,46,40,153,49,208,171])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2464#usize 2496#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [121,222,231,1,61,67,70,17,115,85,96,65,234,200,241,83,60,16,185,45,192,179,155,106,241,106,46,40,153,49,208,171])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [121,222,231,1,61,67,70,17,115,85,96,65,234,200,241,83,60,16,185,45,192,179,155,106,241,106,46,40,153,49,208,171]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [121,222,231,1,61,67,70,17,115,85,96,65,234,200,241,83,60,16,185,45,192,179,155,106,241,106,46,40,153,49,208,171])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2496#usize 2528#usize)=ok (encodeState (JGc_TX2_HashBytes.state [236,28,32,239,13,157,49,221,114,96,197,120,98,199,111,87,83,234,74,238,160,52,25,26,27,9,205,113,23,81,124,152])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2496#usize 2528#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2496#usize 2528#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [236,28,32,239,13,157,49,221,114,96,197,120,98,199,111,87,83,234,74,238,160,52,25,26,27,9,205,113,23,81,124,152])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2496).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35527).take 32)=(encodeState (JGc_TX2_HashBytes.state [236,28,32,239,13,157,49,221,114,96,197,120,98,199,111,87,83,234,74,238,160,52,25,26,27,9,205,113,23,81,124,152])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2496#usize 2528#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [236,28,32,239,13,157,49,221,114,96,197,120,98,199,111,87,83,234,74,238,160,52,25,26,27,9,205,113,23,81,124,152])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [236,28,32,239,13,157,49,221,114,96,197,120,98,199,111,87,83,234,74,238,160,52,25,26,27,9,205,113,23,81,124,152]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [236,28,32,239,13,157,49,221,114,96,197,120,98,199,111,87,83,234,74,238,160,52,25,26,27,9,205,113,23,81,124,152])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2528#usize 2560#usize)=ok (encodeState (JGc_TX2_HashBytes.state [253,228,39,179,67,102,132,204,126,95,1,242,155,20,213,142,13,57,24,198,222,113,242,180,142,143,35,176,242,56,84,56])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2528#usize 2560#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2528#usize 2560#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [253,228,39,179,67,102,132,204,126,95,1,242,155,20,213,142,13,57,24,198,222,113,242,180,142,143,35,176,242,56,84,56])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2528).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35559).take 32)=(encodeState (JGc_TX2_HashBytes.state [253,228,39,179,67,102,132,204,126,95,1,242,155,20,213,142,13,57,24,198,222,113,242,180,142,143,35,176,242,56,84,56])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2528#usize 2560#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [253,228,39,179,67,102,132,204,126,95,1,242,155,20,213,142,13,57,24,198,222,113,242,180,142,143,35,176,242,56,84,56])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [253,228,39,179,67,102,132,204,126,95,1,242,155,20,213,142,13,57,24,198,222,113,242,180,142,143,35,176,242,56,84,56]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [253,228,39,179,67,102,132,204,126,95,1,242,155,20,213,142,13,57,24,198,222,113,242,180,142,143,35,176,242,56,84,56])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 2240) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
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
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 2272#usize)=ok (encodeState (JGc_TX2_HashBytes.state [86,144,167,147,188,24,122,130,134,42,53,1,191,205,208,232,136,53,92,205,132,56,195,95,102,211,36,136,20,102,109,234])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 2272#usize 2176#usize
    512#u32 (encodeState value070) (encodeState (JGc_TX2_HashBytes.state [86,144,167,147,188,24,122,130,134,42,53,1,191,205,208,232,136,53,92,205,132,56,195,95,102,211,36,136,20,102,109,234])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 512#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source080 D hash (s00 s) 1#usize 2272#usize 512#u32 0#usize (by decide)
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
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 2304#usize)=ok (encodeState (JGc_TX2_HashBytes.state [129,134,159,111,208,119,101,44,121,214,241,176,100,83,224,186,157,157,52,15,168,151,4,234,77,57,92,217,53,20,243,178])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 2304#usize 2144#usize
    730#u32 (encodeState value071) (encodeState (JGc_TX2_HashBytes.state [129,134,159,111,208,119,101,44,121,214,241,176,100,83,224,186,157,157,52,15,168,151,4,234,77,57,92,217,53,20,243,178])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 730#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source081 D hash (s01 s) 2#usize 2304#usize 730#u32 1#usize (by decide)
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
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s02 s).«at» 2336#usize)=ok (encodeState (JGc_TX2_HashBytes.state [229,14,215,228,251,27,121,138,26,111,165,216,200,216,201,136,85,212,71,42,31,194,225,192,175,105,184,67,0,188,222,153])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 2#usize 3#usize 2336#usize 2112#usize
    1152#u32 (encodeState value072) (encodeState (JGc_TX2_HashBytes.state [229,14,215,228,251,27,121,138,26,111,165,216,200,216,201,136,85,212,71,42,31,194,225,192,175,105,184,67,0,188,222,153])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read02
  simp only [show 1152#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls1.source082 D hash (s02 s) 3#usize 2336#usize 1152#u32 2#usize (by decide)
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
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s03 s).«at» 2368#usize)=ok (encodeState (JGc_TX2_HashBytes.state [46,123,57,164,118,22,77,38,72,105,83,9,179,113,17,42,45,247,143,151,243,173,174,143,222,205,203,31,224,130,255,177])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 3#usize 4#usize 2368#usize 2080#usize
    1248#u32 (encodeState value073) (encodeState (JGc_TX2_HashBytes.state [46,123,57,164,118,22,77,38,72,105,83,9,179,113,17,42,45,247,143,151,243,173,174,143,222,205,203,31,224,130,255,177])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read03
  simp only [show 1248#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls1.source083 D hash (s03 s) 4#usize 2368#usize 1248#u32 3#usize (by decide)
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
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 2400#usize)=ok (encodeState (JGc_TX2_HashBytes.state [20,207,22,9,174,31,23,223,78,200,11,111,211,240,97,165,212,117,32,89,62,177,230,187,171,248,29,209,77,89,205,216])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 4#usize 5#usize 2400#usize 2048#usize
    1436#u32 (encodeState value074) (encodeState (JGc_TX2_HashBytes.state [20,207,22,9,174,31,23,223,78,200,11,111,211,240,97,165,212,117,32,89,62,177,230,187,171,248,29,209,77,89,205,216])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 1436#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source084 D hash (s04 s) 5#usize 2400#usize 1436#u32 4#usize (by decide)
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
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s05 s).«at» 2432#usize)=ok (encodeState (JGc_TX2_HashBytes.state [152,7,48,143,226,24,235,182,175,169,50,91,216,225,126,157,236,234,179,168,64,123,15,245,94,142,196,215,212,12,175,250])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes1 5#usize 5#usize 6#usize 2432#usize 2016#usize
    1502#u32 (encodeState value075) (encodeState (JGc_TX2_HashBytes.state [152,7,48,143,226,24,235,182,175,169,50,91,216,225,126,157,236,234,179,168,64,123,15,245,94,142,196,215,212,12,175,250])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read05
  simp only [show 1502#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls1.source085 D hash (s05 s) 6#usize 2432#usize 1502#u32 5#usize (by decide)
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
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s06 s).«at» 2464#usize)=ok (encodeState (JGc_TX2_HashBytes.state [152,67,185,114,180,230,228,197,92,49,68,3,243,160,35,107,236,112,86,221,8,66,205,238,116,218,35,5,165,164,99,104])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes1 6#usize 6#usize 7#usize 2464#usize 1984#usize
    1508#u32 (encodeState value076) (encodeState (JGc_TX2_HashBytes.state [152,67,185,114,180,230,228,197,92,49,68,3,243,160,35,107,236,112,86,221,8,66,205,238,116,218,35,5,165,164,99,104])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read06
  simp only [show 1508#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls1.source086 D hash (s06 s) 7#usize 2464#usize 1508#u32 6#usize (by decide)
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
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s07 s).«at» 2496#usize)=ok (encodeState (JGc_TX2_HashBytes.state [121,222,231,1,61,67,70,17,115,85,96,65,234,200,241,83,60,16,185,45,192,179,155,106,241,106,46,40,153,49,208,171])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes1 7#usize 7#usize 8#usize 2496#usize 1952#usize
    1635#u32 (encodeState value077) (encodeState (JGc_TX2_HashBytes.state [121,222,231,1,61,67,70,17,115,85,96,65,234,200,241,83,60,16,185,45,192,179,155,106,241,106,46,40,153,49,208,171])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read07
  simp only [show 1635#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls1.source087 D hash (s07 s) 8#usize 2496#usize 1635#u32 7#usize (by decide)
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
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s08 s).«at» 2528#usize)=ok (encodeState (JGc_TX2_HashBytes.state [236,28,32,239,13,157,49,221,114,96,197,120,98,199,111,87,83,234,74,238,160,52,25,26,27,9,205,113,23,81,124,152])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes1 8#usize 8#usize 9#usize 2528#usize 1920#usize
    1693#u32 (encodeState value078) (encodeState (JGc_TX2_HashBytes.state [236,28,32,239,13,157,49,221,114,96,197,120,98,199,111,87,83,234,74,238,160,52,25,26,27,9,205,113,23,81,124,152])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read08
  simp only [show 1693#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls1.source088 D hash (s08 s) 9#usize 2528#usize 1693#u32 8#usize (by decide)
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
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s09 s).«at» 2560#usize)=ok (encodeState (JGc_TX2_HashBytes.state [253,228,39,179,67,102,132,204,126,95,1,242,155,20,213,142,13,57,24,198,222,113,242,180,142,143,35,176,242,56,84,56])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes1 9#usize 9#usize 10#usize 2560#usize 1888#usize
    1921#u32 (encodeState value079) (encodeState (JGc_TX2_HashBytes.state [253,228,39,179,67,102,132,204,126,95,1,242,155,20,213,142,13,57,24,198,222,113,242,180,142,143,35,176,242,56,84,56])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read09
  simp only [show 1921#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls1.source089 D hash (s09 s) 10#usize 2560#usize 1921#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 2560 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 2528 v09
      1921#u32 9#usize (encodeState value089) 2560#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes1 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 2560
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_07
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_08
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
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
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2560#usize 2592#usize)=ok (encodeState (JGc_TX2_HashBytes.state [155,103,85,214,79,217,145,109,92,61,81,23,89,65,105,137,67,6,203,28,29,132,157,255,203,70,84,95,242,123,36,113])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2560#usize 2592#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2560#usize 2592#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [155,103,85,214,79,217,145,109,92,61,81,23,89,65,105,137,67,6,203,28,29,132,157,255,203,70,84,95,242,123,36,113])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2560).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35591).take 32)=(encodeState (JGc_TX2_HashBytes.state [155,103,85,214,79,217,145,109,92,61,81,23,89,65,105,137,67,6,203,28,29,132,157,255,203,70,84,95,242,123,36,113])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2560#usize 2592#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [155,103,85,214,79,217,145,109,92,61,81,23,89,65,105,137,67,6,203,28,29,132,157,255,203,70,84,95,242,123,36,113])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [155,103,85,214,79,217,145,109,92,61,81,23,89,65,105,137,67,6,203,28,29,132,157,255,203,70,84,95,242,123,36,113]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [155,103,85,214,79,217,145,109,92,61,81,23,89,65,105,137,67,6,203,28,29,132,157,255,203,70,84,95,242,123,36,113])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2592#usize 2624#usize)=ok (encodeState (JGc_TX2_HashBytes.state [58,116,96,190,215,232,35,221,38,191,2,90,224,44,164,216,51,1,133,148,238,15,199,54,87,187,234,15,80,91,124,127])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2592#usize 2624#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2592#usize 2624#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [58,116,96,190,215,232,35,221,38,191,2,90,224,44,164,216,51,1,133,148,238,15,199,54,87,187,234,15,80,91,124,127])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2592).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35623).take 32)=(encodeState (JGc_TX2_HashBytes.state [58,116,96,190,215,232,35,221,38,191,2,90,224,44,164,216,51,1,133,148,238,15,199,54,87,187,234,15,80,91,124,127])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2592#usize 2624#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [58,116,96,190,215,232,35,221,38,191,2,90,224,44,164,216,51,1,133,148,238,15,199,54,87,187,234,15,80,91,124,127])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [58,116,96,190,215,232,35,221,38,191,2,90,224,44,164,216,51,1,133,148,238,15,199,54,87,187,234,15,80,91,124,127]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [58,116,96,190,215,232,35,221,38,191,2,90,224,44,164,216,51,1,133,148,238,15,199,54,87,187,234,15,80,91,124,127])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2624#usize 2656#usize)=ok (encodeState (JGc_TX2_HashBytes.state [102,248,91,151,181,176,166,53,114,57,78,102,66,87,251,100,251,31,205,194,110,147,127,156,193,58,19,3,42,214,148,4])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2624#usize 2656#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2624#usize 2656#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [102,248,91,151,181,176,166,53,114,57,78,102,66,87,251,100,251,31,205,194,110,147,127,156,193,58,19,3,42,214,148,4])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2624).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35655).take 32)=(encodeState (JGc_TX2_HashBytes.state [102,248,91,151,181,176,166,53,114,57,78,102,66,87,251,100,251,31,205,194,110,147,127,156,193,58,19,3,42,214,148,4])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2624#usize 2656#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [102,248,91,151,181,176,166,53,114,57,78,102,66,87,251,100,251,31,205,194,110,147,127,156,193,58,19,3,42,214,148,4])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [102,248,91,151,181,176,166,53,114,57,78,102,66,87,251,100,251,31,205,194,110,147,127,156,193,58,19,3,42,214,148,4]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [102,248,91,151,181,176,166,53,114,57,78,102,66,87,251,100,251,31,205,194,110,147,127,156,193,58,19,3,42,214,148,4])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2656#usize 2688#usize)=ok (encodeState (JGc_TX2_HashBytes.state [181,230,180,31,12,17,59,166,205,11,33,224,169,103,22,14,162,127,69,73,33,189,217,17,98,68,108,205,174,164,64,124])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2656#usize 2688#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2656#usize 2688#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [181,230,180,31,12,17,59,166,205,11,33,224,169,103,22,14,162,127,69,73,33,189,217,17,98,68,108,205,174,164,64,124])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2656).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35687).take 32)=(encodeState (JGc_TX2_HashBytes.state [181,230,180,31,12,17,59,166,205,11,33,224,169,103,22,14,162,127,69,73,33,189,217,17,98,68,108,205,174,164,64,124])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2656#usize 2688#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [181,230,180,31,12,17,59,166,205,11,33,224,169,103,22,14,162,127,69,73,33,189,217,17,98,68,108,205,174,164,64,124])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [181,230,180,31,12,17,59,166,205,11,33,224,169,103,22,14,162,127,69,73,33,189,217,17,98,68,108,205,174,164,64,124]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [181,230,180,31,12,17,59,166,205,11,33,224,169,103,22,14,162,127,69,73,33,189,217,17,98,68,108,205,174,164,64,124])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2688#usize 2720#usize)=ok (encodeState (JGc_TX2_HashBytes.state [190,94,5,136,17,62,168,184,31,168,135,148,106,201,77,251,86,192,166,220,228,214,230,238,13,228,237,219,153,182,6,97])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2688#usize 2720#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2688#usize 2720#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [190,94,5,136,17,62,168,184,31,168,135,148,106,201,77,251,86,192,166,220,228,214,230,238,13,228,237,219,153,182,6,97])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2688).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35719).take 32)=(encodeState (JGc_TX2_HashBytes.state [190,94,5,136,17,62,168,184,31,168,135,148,106,201,77,251,86,192,166,220,228,214,230,238,13,228,237,219,153,182,6,97])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2688#usize 2720#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [190,94,5,136,17,62,168,184,31,168,135,148,106,201,77,251,86,192,166,220,228,214,230,238,13,228,237,219,153,182,6,97])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [190,94,5,136,17,62,168,184,31,168,135,148,106,201,77,251,86,192,166,220,228,214,230,238,13,228,237,219,153,182,6,97]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [190,94,5,136,17,62,168,184,31,168,135,148,106,201,77,251,86,192,166,220,228,214,230,238,13,228,237,219,153,182,6,97])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2720#usize 2752#usize)=ok (encodeState (JGc_TX2_HashBytes.state [101,117,98,190,161,169,31,147,28,228,55,74,81,235,49,28,180,213,167,50,32,72,106,99,146,44,200,203,152,20,148,224])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2720#usize 2752#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2720#usize 2752#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [101,117,98,190,161,169,31,147,28,228,55,74,81,235,49,28,180,213,167,50,32,72,106,99,146,44,200,203,152,20,148,224])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2720).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35751).take 32)=(encodeState (JGc_TX2_HashBytes.state [101,117,98,190,161,169,31,147,28,228,55,74,81,235,49,28,180,213,167,50,32,72,106,99,146,44,200,203,152,20,148,224])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2720#usize 2752#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [101,117,98,190,161,169,31,147,28,228,55,74,81,235,49,28,180,213,167,50,32,72,106,99,146,44,200,203,152,20,148,224])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [101,117,98,190,161,169,31,147,28,228,55,74,81,235,49,28,180,213,167,50,32,72,106,99,146,44,200,203,152,20,148,224]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [101,117,98,190,161,169,31,147,28,228,55,74,81,235,49,28,180,213,167,50,32,72,106,99,146,44,200,203,152,20,148,224])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2752#usize 2784#usize)=ok (encodeState (JGc_TX2_HashBytes.state [141,78,139,205,243,175,85,174,159,6,241,87,39,153,190,45,228,30,233,41,84,56,127,174,209,151,54,93,242,26,164,0])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2752#usize 2784#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2752#usize 2784#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [141,78,139,205,243,175,85,174,159,6,241,87,39,153,190,45,228,30,233,41,84,56,127,174,209,151,54,93,242,26,164,0])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2752).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35783).take 32)=(encodeState (JGc_TX2_HashBytes.state [141,78,139,205,243,175,85,174,159,6,241,87,39,153,190,45,228,30,233,41,84,56,127,174,209,151,54,93,242,26,164,0])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2752#usize 2784#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [141,78,139,205,243,175,85,174,159,6,241,87,39,153,190,45,228,30,233,41,84,56,127,174,209,151,54,93,242,26,164,0])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [141,78,139,205,243,175,85,174,159,6,241,87,39,153,190,45,228,30,233,41,84,56,127,174,209,151,54,93,242,26,164,0]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [141,78,139,205,243,175,85,174,159,6,241,87,39,153,190,45,228,30,233,41,84,56,127,174,209,151,54,93,242,26,164,0])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2784#usize 2816#usize)=ok (encodeState (JGc_TX2_HashBytes.state [243,43,79,171,171,236,158,171,6,102,177,162,155,60,85,93,158,195,157,106,68,63,238,61,71,98,3,55,236,229,85,103])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2784#usize 2816#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2784#usize 2816#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [243,43,79,171,171,236,158,171,6,102,177,162,155,60,85,93,158,195,157,106,68,63,238,61,71,98,3,55,236,229,85,103])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2784).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35815).take 32)=(encodeState (JGc_TX2_HashBytes.state [243,43,79,171,171,236,158,171,6,102,177,162,155,60,85,93,158,195,157,106,68,63,238,61,71,98,3,55,236,229,85,103])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2784#usize 2816#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [243,43,79,171,171,236,158,171,6,102,177,162,155,60,85,93,158,195,157,106,68,63,238,61,71,98,3,55,236,229,85,103])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [243,43,79,171,171,236,158,171,6,102,177,162,155,60,85,93,158,195,157,106,68,63,238,61,71,98,3,55,236,229,85,103]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [243,43,79,171,171,236,158,171,6,102,177,162,155,60,85,93,158,195,157,106,68,63,238,61,71,98,3,55,236,229,85,103])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2816#usize 2848#usize)=ok (encodeState (JGc_TX2_HashBytes.state [0,59,195,249,83,130,210,170,7,120,9,195,215,100,15,59,6,122,239,166,176,134,205,3,143,184,111,215,61,93,21,205])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2816#usize 2848#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2816#usize 2848#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [0,59,195,249,83,130,210,170,7,120,9,195,215,100,15,59,6,122,239,166,176,134,205,3,143,184,111,215,61,93,21,205])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2816).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35847).take 32)=(encodeState (JGc_TX2_HashBytes.state [0,59,195,249,83,130,210,170,7,120,9,195,215,100,15,59,6,122,239,166,176,134,205,3,143,184,111,215,61,93,21,205])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2816#usize 2848#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [0,59,195,249,83,130,210,170,7,120,9,195,215,100,15,59,6,122,239,166,176,134,205,3,143,184,111,215,61,93,21,205])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [0,59,195,249,83,130,210,170,7,120,9,195,215,100,15,59,6,122,239,166,176,134,205,3,143,184,111,215,61,93,21,205]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [0,59,195,249,83,130,210,170,7,120,9,195,215,100,15,59,6,122,239,166,176,134,205,3,143,184,111,215,61,93,21,205])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2848#usize 2880#usize)=ok (encodeState (JGc_TX2_HashBytes.state [30,110,144,85,51,255,13,5,112,59,188,211,168,27,244,37,155,108,73,250,65,218,219,68,254,71,61,200,99,148,247,126])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2848#usize 2880#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2848#usize 2880#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [30,110,144,85,51,255,13,5,112,59,188,211,168,27,244,37,155,108,73,250,65,218,219,68,254,71,61,200,99,148,247,126])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2848).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35879).take 32)=(encodeState (JGc_TX2_HashBytes.state [30,110,144,85,51,255,13,5,112,59,188,211,168,27,244,37,155,108,73,250,65,218,219,68,254,71,61,200,99,148,247,126])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2848#usize 2880#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [30,110,144,85,51,255,13,5,112,59,188,211,168,27,244,37,155,108,73,250,65,218,219,68,254,71,61,200,99,148,247,126])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [30,110,144,85,51,255,13,5,112,59,188,211,168,27,244,37,155,108,73,250,65,218,219,68,254,71,61,200,99,148,247,126]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [30,110,144,85,51,255,13,5,112,59,188,211,168,27,244,37,155,108,73,250,65,218,219,68,254,71,61,200,99,148,247,126])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 2560) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
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
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 2592#usize)=ok (encodeState (JGc_TX2_HashBytes.state [155,103,85,214,79,217,145,109,92,61,81,23,89,65,105,137,67,6,203,28,29,132,157,255,203,70,84,95,242,123,36,113])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 2592#usize 1856#usize
    256#u32 (encodeState value080) (encodeState (JGc_TX2_HashBytes.state [155,103,85,214,79,217,145,109,92,61,81,23,89,65,105,137,67,6,203,28,29,132,157,255,203,70,84,95,242,123,36,113])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 256#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source090 D hash (s00 s) 1#usize 2592#usize 256#u32 0#usize (by decide)
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
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 2624#usize)=ok (encodeState (JGc_TX2_HashBytes.state [58,116,96,190,215,232,35,221,38,191,2,90,224,44,164,216,51,1,133,148,238,15,199,54,87,187,234,15,80,91,124,127])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 2624#usize 1824#usize
    365#u32 (encodeState value081) (encodeState (JGc_TX2_HashBytes.state [58,116,96,190,215,232,35,221,38,191,2,90,224,44,164,216,51,1,133,148,238,15,199,54,87,187,234,15,80,91,124,127])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 365#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source091 D hash (s01 s) 2#usize 2624#usize 365#u32 1#usize (by decide)
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
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s02 s).«at» 2656#usize)=ok (encodeState (JGc_TX2_HashBytes.state [102,248,91,151,181,176,166,53,114,57,78,102,66,87,251,100,251,31,205,194,110,147,127,156,193,58,19,3,42,214,148,4])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 2#usize 3#usize 2656#usize 1792#usize
    576#u32 (encodeState value082) (encodeState (JGc_TX2_HashBytes.state [102,248,91,151,181,176,166,53,114,57,78,102,66,87,251,100,251,31,205,194,110,147,127,156,193,58,19,3,42,214,148,4])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read02
  simp only [show 576#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls1.source092 D hash (s02 s) 3#usize 2656#usize 576#u32 2#usize (by decide)
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
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s03 s).«at» 2688#usize)=ok (encodeState (JGc_TX2_HashBytes.state [181,230,180,31,12,17,59,166,205,11,33,224,169,103,22,14,162,127,69,73,33,189,217,17,98,68,108,205,174,164,64,124])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 3#usize 4#usize 2688#usize 1760#usize
    624#u32 (encodeState value083) (encodeState (JGc_TX2_HashBytes.state [181,230,180,31,12,17,59,166,205,11,33,224,169,103,22,14,162,127,69,73,33,189,217,17,98,68,108,205,174,164,64,124])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read03
  simp only [show 624#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls1.source093 D hash (s03 s) 4#usize 2688#usize 624#u32 3#usize (by decide)
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
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 2720#usize)=ok (encodeState (JGc_TX2_HashBytes.state [190,94,5,136,17,62,168,184,31,168,135,148,106,201,77,251,86,192,166,220,228,214,230,238,13,228,237,219,153,182,6,97])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 4#usize 5#usize 2720#usize 1728#usize
    718#u32 (encodeState value084) (encodeState (JGc_TX2_HashBytes.state [190,94,5,136,17,62,168,184,31,168,135,148,106,201,77,251,86,192,166,220,228,214,230,238,13,228,237,219,153,182,6,97])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 718#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source094 D hash (s04 s) 5#usize 2720#usize 718#u32 4#usize (by decide)
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
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s05 s).«at» 2752#usize)=ok (encodeState (JGc_TX2_HashBytes.state [101,117,98,190,161,169,31,147,28,228,55,74,81,235,49,28,180,213,167,50,32,72,106,99,146,44,200,203,152,20,148,224])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes1 5#usize 5#usize 6#usize 2752#usize 1696#usize
    751#u32 (encodeState value085) (encodeState (JGc_TX2_HashBytes.state [101,117,98,190,161,169,31,147,28,228,55,74,81,235,49,28,180,213,167,50,32,72,106,99,146,44,200,203,152,20,148,224])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read05
  simp only [show 751#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls1.source095 D hash (s05 s) 6#usize 2752#usize 751#u32 5#usize (by decide)
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
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s06 s).«at» 2784#usize)=ok (encodeState (JGc_TX2_HashBytes.state [141,78,139,205,243,175,85,174,159,6,241,87,39,153,190,45,228,30,233,41,84,56,127,174,209,151,54,93,242,26,164,0])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes1 6#usize 6#usize 7#usize 2784#usize 1664#usize
    754#u32 (encodeState value086) (encodeState (JGc_TX2_HashBytes.state [141,78,139,205,243,175,85,174,159,6,241,87,39,153,190,45,228,30,233,41,84,56,127,174,209,151,54,93,242,26,164,0])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read06
  simp only [show 754#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls1.source096 D hash (s06 s) 7#usize 2784#usize 754#u32 6#usize (by decide)
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
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s07 s).«at» 2816#usize)=ok (encodeState (JGc_TX2_HashBytes.state [243,43,79,171,171,236,158,171,6,102,177,162,155,60,85,93,158,195,157,106,68,63,238,61,71,98,3,55,236,229,85,103])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes1 7#usize 7#usize 8#usize 2816#usize 1632#usize
    817#u32 (encodeState value087) (encodeState (JGc_TX2_HashBytes.state [243,43,79,171,171,236,158,171,6,102,177,162,155,60,85,93,158,195,157,106,68,63,238,61,71,98,3,55,236,229,85,103])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read07
  simp only [show 817#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls1.source097 D hash (s07 s) 8#usize 2816#usize 817#u32 7#usize (by decide)
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
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s08 s).«at» 2848#usize)=ok (encodeState (JGc_TX2_HashBytes.state [0,59,195,249,83,130,210,170,7,120,9,195,215,100,15,59,6,122,239,166,176,134,205,3,143,184,111,215,61,93,21,205])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes1 8#usize 8#usize 9#usize 2848#usize 1600#usize
    846#u32 (encodeState value088) (encodeState (JGc_TX2_HashBytes.state [0,59,195,249,83,130,210,170,7,120,9,195,215,100,15,59,6,122,239,166,176,134,205,3,143,184,111,215,61,93,21,205])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read08
  simp only [show 846#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls1.source098 D hash (s08 s) 9#usize 2848#usize 846#u32 8#usize (by decide)
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
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s09 s).«at» 2880#usize)=ok (encodeState (JGc_TX2_HashBytes.state [30,110,144,85,51,255,13,5,112,59,188,211,168,27,244,37,155,108,73,250,65,218,219,68,254,71,61,200,99,148,247,126])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes1 9#usize 9#usize 10#usize 2880#usize 1568#usize
    960#u32 (encodeState value089) (encodeState (JGc_TX2_HashBytes.state [30,110,144,85,51,255,13,5,112,59,188,211,168,27,244,37,155,108,73,250,65,218,219,68,254,71,61,200,99,148,247,126])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read09
  simp only [show 960#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls1.source099 D hash (s09 s) 10#usize 2880#usize 960#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 2880 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 2848 v09
      960#u32 9#usize (encodeState value099) 2880#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes1 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 2880
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_08
end


end
