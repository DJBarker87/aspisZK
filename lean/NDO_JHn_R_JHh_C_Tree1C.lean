import NDO_JHn_R_JHh_C_Tree1C_B
import RPt_JFq_Range
import NDO_JFw_Frames
import JGm_TX2_HeightTools
import NDO_JGm_TX2_View
import NDO_JGr_Counts
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
namespace AspisR1.JHh_C_Gu_Level1_12
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [16#u32,22#u32,36#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
def values00 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 16#u32 0#usize (encodeState value130) 3872#usize
 def indices01 : List U32 := [8#u32,22#u32,36#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value130,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 22#u32 1#usize (encodeState value131) 3904#usize
 def indices02 : List U32 := [8#u32,11#u32,36#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 36#u32 2#usize (encodeState value132) 3936#usize
 def indices03 : List U32 := [8#u32,11#u32,18#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 39#u32 3#usize (encodeState value133) 3968#usize
 def indices04 : List U32 := [8#u32,11#u32,18#u32,19#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 44#u32 4#usize (encodeState value134) 4000#usize
 def indices05 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 46#u32 5#usize (encodeState value135) 4000#usize
 def indices06 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,47#u32,51#u32,52#u32,60#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 51#u32 6#usize (encodeState value136) 4032#usize
 def indices07 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,51#u32,52#u32,60#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value127,encodeState value128,encodeState value129]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 52#u32 7#usize (encodeState value137) 4064#usize
 def indices08 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,52#u32,60#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value128,encodeState value129]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 60#u32 8#usize (encodeState value138) 4096#usize
 def indices09 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32,60#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value129]
def output (s : reference.Scratch) : reference.Scratch := {s09 s with n:=9#usize}
 def indicesOut : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3840#usize 3872#usize)=ok (encodeState (JGc_TX2_HashBytes.state [19,103,232,182,95,97,172,122,95,102,130,230,233,176,203,8,117,127,219,234,112,18,233,156,196,18,149,209,241,77,161,56])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3840#usize 3872#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3840#usize 3872#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [19,103,232,182,95,97,172,122,95,102,130,230,233,176,203,8,117,127,219,234,112,18,233,156,196,18,149,209,241,77,161,56])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3840).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36871).take 32)=(encodeState (JGc_TX2_HashBytes.state [19,103,232,182,95,97,172,122,95,102,130,230,233,176,203,8,117,127,219,234,112,18,233,156,196,18,149,209,241,77,161,56])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3840#usize 3872#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [19,103,232,182,95,97,172,122,95,102,130,230,233,176,203,8,117,127,219,234,112,18,233,156,196,18,149,209,241,77,161,56])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [19,103,232,182,95,97,172,122,95,102,130,230,233,176,203,8,117,127,219,234,112,18,233,156,196,18,149,209,241,77,161,56]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [19,103,232,182,95,97,172,122,95,102,130,230,233,176,203,8,117,127,219,234,112,18,233,156,196,18,149,209,241,77,161,56])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3872#usize 3904#usize)=ok (encodeState (JGc_TX2_HashBytes.state [110,25,47,112,26,76,158,29,84,93,93,101,136,114,133,182,113,217,50,169,101,168,154,202,147,239,155,119,156,1,149,227])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3872#usize 3904#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3872#usize 3904#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [110,25,47,112,26,76,158,29,84,93,93,101,136,114,133,182,113,217,50,169,101,168,154,202,147,239,155,119,156,1,149,227])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3872).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36903).take 32)=(encodeState (JGc_TX2_HashBytes.state [110,25,47,112,26,76,158,29,84,93,93,101,136,114,133,182,113,217,50,169,101,168,154,202,147,239,155,119,156,1,149,227])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3872#usize 3904#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [110,25,47,112,26,76,158,29,84,93,93,101,136,114,133,182,113,217,50,169,101,168,154,202,147,239,155,119,156,1,149,227])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [110,25,47,112,26,76,158,29,84,93,93,101,136,114,133,182,113,217,50,169,101,168,154,202,147,239,155,119,156,1,149,227]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [110,25,47,112,26,76,158,29,84,93,93,101,136,114,133,182,113,217,50,169,101,168,154,202,147,239,155,119,156,1,149,227])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3904#usize 3936#usize)=ok (encodeState (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3904#usize 3936#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3904#usize 3936#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3904).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36935).take 32)=(encodeState (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3904#usize 3936#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3936#usize 3968#usize)=ok (encodeState (JGc_TX2_HashBytes.state [202,244,232,254,150,185,96,120,137,19,88,126,27,134,33,218,94,250,191,155,104,44,152,222,79,170,78,156,230,59,10,83])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3936#usize 3968#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3936#usize 3968#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [202,244,232,254,150,185,96,120,137,19,88,126,27,134,33,218,94,250,191,155,104,44,152,222,79,170,78,156,230,59,10,83])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3936).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36967).take 32)=(encodeState (JGc_TX2_HashBytes.state [202,244,232,254,150,185,96,120,137,19,88,126,27,134,33,218,94,250,191,155,104,44,152,222,79,170,78,156,230,59,10,83])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3936#usize 3968#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [202,244,232,254,150,185,96,120,137,19,88,126,27,134,33,218,94,250,191,155,104,44,152,222,79,170,78,156,230,59,10,83])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [202,244,232,254,150,185,96,120,137,19,88,126,27,134,33,218,94,250,191,155,104,44,152,222,79,170,78,156,230,59,10,83]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [202,244,232,254,150,185,96,120,137,19,88,126,27,134,33,218,94,250,191,155,104,44,152,222,79,170,78,156,230,59,10,83])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3968#usize 4000#usize)=ok (encodeState (JGc_TX2_HashBytes.state [166,50,145,224,172,240,239,69,50,244,235,90,162,220,82,237,69,91,183,14,206,124,87,33,164,12,204,235,137,70,174,5])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3968#usize 4000#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3968#usize 4000#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [166,50,145,224,172,240,239,69,50,244,235,90,162,220,82,237,69,91,183,14,206,124,87,33,164,12,204,235,137,70,174,5])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3968).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36999).take 32)=(encodeState (JGc_TX2_HashBytes.state [166,50,145,224,172,240,239,69,50,244,235,90,162,220,82,237,69,91,183,14,206,124,87,33,164,12,204,235,137,70,174,5])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3968#usize 4000#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [166,50,145,224,172,240,239,69,50,244,235,90,162,220,82,237,69,91,183,14,206,124,87,33,164,12,204,235,137,70,174,5])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [166,50,145,224,172,240,239,69,50,244,235,90,162,220,82,237,69,91,183,14,206,124,87,33,164,12,204,235,137,70,174,5]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [166,50,145,224,172,240,239,69,50,244,235,90,162,220,82,237,69,91,183,14,206,124,87,33,164,12,204,235,137,70,174,5])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      4000#usize 4032#usize)=ok (encodeState (JGc_TX2_HashBytes.state [153,133,221,15,146,6,115,140,230,185,130,26,225,15,86,62,76,251,182,229,99,145,33,151,46,29,16,78,20,210,184,89])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4000#usize 4032#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 4000#usize 4032#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [153,133,221,15,146,6,115,140,230,185,130,26,225,15,86,62,76,251,182,229,99,145,33,151,46,29,16,78,20,210,184,89])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 4000).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37031).take 32)=(encodeState (JGc_TX2_HashBytes.state [153,133,221,15,146,6,115,140,230,185,130,26,225,15,86,62,76,251,182,229,99,145,33,151,46,29,16,78,20,210,184,89])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 4000#usize 4032#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [153,133,221,15,146,6,115,140,230,185,130,26,225,15,86,62,76,251,182,229,99,145,33,151,46,29,16,78,20,210,184,89])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [153,133,221,15,146,6,115,140,230,185,130,26,225,15,86,62,76,251,182,229,99,145,33,151,46,29,16,78,20,210,184,89]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [153,133,221,15,146,6,115,140,230,185,130,26,225,15,86,62,76,251,182,229,99,145,33,151,46,29,16,78,20,210,184,89])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      4032#usize 4064#usize)=ok (encodeState (JGc_TX2_HashBytes.state [66,199,69,31,236,191,95,45,107,250,179,40,169,78,64,209,27,26,172,83,225,86,252,237,38,168,176,210,39,212,103,98])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4032#usize 4064#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 4032#usize 4064#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [66,199,69,31,236,191,95,45,107,250,179,40,169,78,64,209,27,26,172,83,225,86,252,237,38,168,176,210,39,212,103,98])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 4032).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37063).take 32)=(encodeState (JGc_TX2_HashBytes.state [66,199,69,31,236,191,95,45,107,250,179,40,169,78,64,209,27,26,172,83,225,86,252,237,38,168,176,210,39,212,103,98])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 4032#usize 4064#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [66,199,69,31,236,191,95,45,107,250,179,40,169,78,64,209,27,26,172,83,225,86,252,237,38,168,176,210,39,212,103,98])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [66,199,69,31,236,191,95,45,107,250,179,40,169,78,64,209,27,26,172,83,225,86,252,237,38,168,176,210,39,212,103,98]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [66,199,69,31,236,191,95,45,107,250,179,40,169,78,64,209,27,26,172,83,225,86,252,237,38,168,176,210,39,212,103,98])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      4064#usize 4096#usize)=ok (encodeState (JGc_TX2_HashBytes.state [235,175,68,146,148,50,230,240,90,237,138,62,236,194,107,145,48,135,75,194,84,203,138,124,153,6,202,37,189,117,252,127])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4064#usize 4096#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 4064#usize 4096#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [235,175,68,146,148,50,230,240,90,237,138,62,236,194,107,145,48,135,75,194,84,203,138,124,153,6,202,37,189,117,252,127])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 4064).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37095).take 32)=(encodeState (JGc_TX2_HashBytes.state [235,175,68,146,148,50,230,240,90,237,138,62,236,194,107,145,48,135,75,194,84,203,138,124,153,6,202,37,189,117,252,127])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 4064#usize 4096#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [235,175,68,146,148,50,230,240,90,237,138,62,236,194,107,145,48,135,75,194,84,203,138,124,153,6,202,37,189,117,252,127])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [235,175,68,146,148,50,230,240,90,237,138,62,236,194,107,145,48,135,75,194,84,203,138,124,153,6,202,37,189,117,252,127]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [235,175,68,146,148,50,230,240,90,237,138,62,236,194,107,145,48,135,75,194,84,203,138,124,153,6,202,37,189,117,252,127])).property];decide)
  exact same ▸ run
#print axioms read08
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3840) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 4096 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3840 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 16#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3840 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value120) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3840 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3840#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠16#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨22#u32,JGm_TX2_View.index (s00 s) indices00 values00 3840 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 3872#usize)=ok (encodeState (JGc_TX2_HashBytes.state [19,103,232,182,95,97,172,122,95,102,130,230,233,176,203,8,117,127,219,234,112,18,233,156,196,18,149,209,241,77,161,56])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 3872#usize 576#usize
    16#u32 (encodeState value120) (encodeState (JGc_TX2_HashBytes.state [19,103,232,182,95,97,172,122,95,102,130,230,233,176,203,8,117,127,219,234,112,18,233,156,196,18,149,209,241,77,161,56])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 16#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source130 D hash (s00 s) 1#usize 3872#usize 16#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3872 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3840 v00
      16#u32 0#usize (encodeState value130) 3872#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 22#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 3872 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value121) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3872 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=3872#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠22#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨36#u32,JGm_TX2_View.index (s01 s) indices01 values01 3872 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 3904#usize)=ok (encodeState (JGc_TX2_HashBytes.state [110,25,47,112,26,76,158,29,84,93,93,101,136,114,133,182,113,217,50,169,101,168,154,202,147,239,155,119,156,1,149,227])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 3904#usize 544#usize
    22#u32 (encodeState value121) (encodeState (JGc_TX2_HashBytes.state [110,25,47,112,26,76,158,29,84,93,93,101,136,114,133,182,113,217,50,169,101,168,154,202,147,239,155,119,156,1,149,227])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 22#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source131 D hash (s01 s) 2#usize 3904#usize 22#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 3904 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 3872 v01
      22#u32 1#usize (encodeState value131) 3904#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 36#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 3904 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value122) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3904 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=3904#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠36#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨39#u32,JGm_TX2_View.index (s02 s) indices02 values02 3904 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s02 s).«at» 3936#usize)=ok (encodeState (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 2#usize 3#usize 3936#usize 512#usize
    36#u32 (encodeState value122) (encodeState (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read02
  simp only [show 36#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls1.source132 D hash (s02 s) 3#usize 3936#usize 36#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 3936 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 3904 v02
      36#u32 2#usize (encodeState value132) 3936#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 39#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 3936 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value123) :=
    JGm_TX2_View.value (s03 s) indices03 values03 3936 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=3936#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠39#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨44#u32,JGm_TX2_View.index (s03 s) indices03 values03 3936 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s03 s).«at» 3968#usize)=ok (encodeState (JGc_TX2_HashBytes.state [202,244,232,254,150,185,96,120,137,19,88,126,27,134,33,218,94,250,191,155,104,44,152,222,79,170,78,156,230,59,10,83])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 3#usize 4#usize 3968#usize 480#usize
    39#u32 (encodeState value123) (encodeState (JGc_TX2_HashBytes.state [202,244,232,254,150,185,96,120,137,19,88,126,27,134,33,218,94,250,191,155,104,44,152,222,79,170,78,156,230,59,10,83])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read03
  simp only [show 39#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls1.source133 D hash (s03 s) 4#usize 3968#usize 39#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 3968 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 3936 v03
      39#u32 3#usize (encodeState value133) 3968#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 44#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 3968 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value124) :=
    JGm_TX2_View.value (s04 s) indices04 values04 3968 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=3968#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠44#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨46#u32,JGm_TX2_View.index (s04 s) indices04 values04 3968 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 4000#usize)=ok (encodeState (JGc_TX2_HashBytes.state [166,50,145,224,172,240,239,69,50,244,235,90,162,220,82,237,69,91,183,14,206,124,87,33,164,12,204,235,137,70,174,5])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 4#usize 5#usize 4000#usize 448#usize
    44#u32 (encodeState value124) (encodeState (JGc_TX2_HashBytes.state [166,50,145,224,172,240,239,69,50,244,235,90,162,220,82,237,69,91,183,14,206,124,87,33,164,12,204,235,137,70,174,5])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 44#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source134 D hash (s04 s) 5#usize 4000#usize 44#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 4000 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 3968 v04
      44#u32 4#usize (encodeState value134) 4000#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 46#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 4000 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value125) :=
    JGm_TX2_View.value (s05 s) indices05 values05 4000 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=4000#usize := UScalar.eq_of_val_eq v05.at_eq
  have rn05 : Array.index_usize (s05 s).idx 6#usize=ok (46#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s05 s) indices05 values05 4000 v05 6#usize (by decide)
  have rr05 : Array.index_usize (s05 s).val 6#usize=ok (encodeState value126) :=
    JGm_TX2_View.value (s05 s) indices05 values05 4000 v05 6#usize (by decide)
  have selected05 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes1 5#usize 5#usize 6#usize 7#usize 46#u32
    (encodeState value125) (encodeState value126) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (6:Nat)<(s05 s).n.val;rw [v05.size];decide)
    rn05 rr05 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 7#usize 6#usize) := by
    rw [selected05]
    rw [cursor05]
    exact JHh_C_Gu_ParentCalls1.source135 D hash (s05 s) 7#usize 4000#usize 46#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 4000 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 4000 v05
      46#u32 5#usize (encodeState value135) 4000#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 7#usize=ok 51#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 4000 v06 7#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 7#usize=ok (encodeState value127) :=
    JGm_TX2_View.value (s06 s) indices06 values06 4000 v06 7#usize (by decide)
  have active06 : 7#usize<(s06 s).n := by
    change (7:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=4000#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 8#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 8#usize=ok other ∧ other≠51#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨52#u32,JGm_TX2_View.index (s06 s) indices06 values06 4000 v06 8#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s06 s).«at» 4032#usize)=ok (encodeState (JGc_TX2_HashBytes.state [153,133,221,15,146,6,115,140,230,185,130,26,225,15,86,62,76,251,182,229,99,145,33,151,46,29,16,78,20,210,184,89])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes1 7#usize 6#usize 8#usize 4032#usize 416#usize
    51#u32 (encodeState value127) (encodeState (JGc_TX2_HashBytes.state [153,133,221,15,146,6,115,140,230,185,130,26,225,15,86,62,76,251,182,229,99,145,33,151,46,29,16,78,20,210,184,89])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read06
  simp only [show 51#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes1 7#usize 6#usize=
        ok (.Next (s07 s) 8#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls1.source136 D hash (s06 s) 8#usize 4032#usize 51#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 4032 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 4000 v06
      51#u32 6#usize (encodeState value136) 4032#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 8#usize=ok 52#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 4032 v07 8#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 8#usize=ok (encodeState value128) :=
    JGm_TX2_View.value (s07 s) indices07 values07 4032 v07 8#usize (by decide)
  have active07 : 8#usize<(s07 s).n := by
    change (8:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=4032#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 9#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 9#usize=ok other ∧ other≠52#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨60#u32,JGm_TX2_View.index (s07 s) indices07 values07 4032 v07 9#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s07 s).«at» 4064#usize)=ok (encodeState (JGc_TX2_HashBytes.state [66,199,69,31,236,191,95,45,107,250,179,40,169,78,64,209,27,26,172,83,225,86,252,237,38,168,176,210,39,212,103,98])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes1 8#usize 7#usize 9#usize 4064#usize 384#usize
    52#u32 (encodeState value128) (encodeState (JGc_TX2_HashBytes.state [66,199,69,31,236,191,95,45,107,250,179,40,169,78,64,209,27,26,172,83,225,86,252,237,38,168,176,210,39,212,103,98])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read07
  simp only [show 52#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes1 8#usize 7#usize=
        ok (.Next (s08 s) 9#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls1.source137 D hash (s07 s) 9#usize 4064#usize 52#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 4064 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 4032 v07
      52#u32 7#usize (encodeState value137) 4064#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 9#usize=ok 60#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 4064 v08 9#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 9#usize=ok (encodeState value129) :=
    JGm_TX2_View.value (s08 s) indices08 values08 4064 v08 9#usize (by decide)
  have active08 : 9#usize<(s08 s).n := by
    change (9:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=4064#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 10#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 10#usize=ok other ∧ other≠60#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s08 s).n.val at more
    rw [v08.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s08 s).«at» 4096#usize)=ok (encodeState (JGc_TX2_HashBytes.state [235,175,68,146,148,50,230,240,90,237,138,62,236,194,107,145,48,135,75,194,84,203,138,124,153,6,202,37,189,117,252,127])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes1 9#usize 8#usize 10#usize 4096#usize 352#usize
    60#u32 (encodeState value129) (encodeState (JGc_TX2_HashBytes.state [235,175,68,146,148,50,230,240,90,237,138,62,236,194,107,145,48,135,75,194,84,203,138,124,153,6,202,37,189,117,252,127])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read08
  simp only [show 60#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes1 9#usize 8#usize=
        ok (.Next (s09 s) 10#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls1.source138 D hash (s08 s) 10#usize 4096#usize 60#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 4096 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 4064 v08
      60#u32 8#usize (encodeState value138) 4096#usize (by decide)
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
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes1 7#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes1 8#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes1 9#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes1 10#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s09 s).n.val≤10;rw [v09.size];decide)
  · exact JGm_TX2_View.finish (s09 s) indices09 values09 4096
      v09 9#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_12
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_13
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
def values00 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 8#u32 0#usize (encodeState value139) 4128#usize
 def indices01 : List U32 := [4#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value139,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 11#u32 1#usize (encodeState value140) 4160#usize
 def indices02 : List U32 := [4#u32,5#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 18#u32 2#usize (encodeState value141) 4160#usize
 def indices03 : List U32 := [4#u32,5#u32,9#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value141,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 22#u32 3#usize (encodeState value142) 4160#usize
 def indices04 : List U32 := [4#u32,5#u32,9#u32,11#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 25#u32 4#usize (encodeState value143) 4192#usize
 def indices05 : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,23#u32,25#u32,26#u32,30#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143,encodeState value135,encodeState value136,encodeState value137,encodeState value138]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 26#u32 5#usize (encodeState value144) 4224#usize
 def indices06 : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,13#u32,25#u32,26#u32,30#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143,encodeState value144,encodeState value136,encodeState value137,encodeState value138]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 30#u32 6#usize (encodeState value145) 4256#usize
 def indices07 : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,13#u32,15#u32,26#u32,30#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143,encodeState value144,encodeState value145,encodeState value137,encodeState value138]
def output (s : reference.Scratch) : reference.Scratch := {s07 s with n:=7#usize}
 def indicesOut : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,13#u32,15#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143,encodeState value144,encodeState value145]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      4096#usize 4128#usize)=ok (encodeState (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4096#usize 4128#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 4096#usize 4128#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 4096).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37127).take 32)=(encodeState (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 4096#usize 4128#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      4128#usize 4160#usize)=ok (encodeState (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4128#usize 4160#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 4128#usize 4160#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 4128).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37159).take 32)=(encodeState (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 4128#usize 4160#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      4160#usize 4192#usize)=ok (encodeState (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4160#usize 4192#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 4160#usize 4192#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 4160).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37191).take 32)=(encodeState (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 4160#usize 4192#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      4192#usize 4224#usize)=ok (encodeState (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4192#usize 4224#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 4192#usize 4224#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 4192).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37223).take 32)=(encodeState (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 4192#usize 4224#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      4224#usize 4256#usize)=ok (encodeState (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4224#usize 4256#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 4224#usize 4256#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 4224).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37255).take 32)=(encodeState (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 4224#usize 4256#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2])).property];decide)
  exact same ▸ run
#print axioms read06
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 4096) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 4256 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 4096 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 8#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 4096 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value130) :=
    JGm_TX2_View.value (s00 s) indices00 values00 4096 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=4096#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠8#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨11#u32,JGm_TX2_View.index (s00 s) indices00 values00 4096 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 4128#usize)=ok (encodeState (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 4128#usize 320#usize
    8#u32 (encodeState value130) (encodeState (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 8#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source139 D hash (s00 s) 1#usize 4128#usize 8#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 4128 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 4096 v00
      8#u32 0#usize (encodeState value139) 4128#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 11#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 4128 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value131) :=
    JGm_TX2_View.value (s01 s) indices01 values01 4128 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=4128#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠11#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨18#u32,JGm_TX2_View.index (s01 s) indices01 values01 4128 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 4160#usize)=ok (encodeState (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 4160#usize 288#usize
    11#u32 (encodeState value131) (encodeState (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 11#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source140 D hash (s01 s) 2#usize 4160#usize 11#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 4160 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 4128 v01
      11#u32 1#usize (encodeState value140) 4160#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 18#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 4160 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value132) :=
    JGm_TX2_View.value (s02 s) indices02 values02 4160 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=4160#usize := UScalar.eq_of_val_eq v02.at_eq
  have rn02 : Array.index_usize (s02 s).idx 3#usize=ok (18#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s02 s) indices02 values02 4160 v02 3#usize (by decide)
  have rr02 : Array.index_usize (s02 s).val 3#usize=ok (encodeState value133) :=
    JGm_TX2_View.value (s02 s) indices02 values02 4160 v02 3#usize (by decide)
  have selected02 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 2#usize 3#usize 4#usize 18#u32
    (encodeState value132) (encodeState value133) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (3:Nat)<(s02 s).n.val;rw [v02.size];decide)
    rn02 rr02 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 4#usize 3#usize) := by
    rw [selected02]
    rw [cursor02]
    exact JHh_C_Gu_ParentCalls1.source141 D hash (s02 s) 4#usize 4160#usize 18#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 4160 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 4160 v02
      18#u32 2#usize (encodeState value141) 4160#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 4#usize=ok 22#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 4160 v03 4#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 4#usize=ok (encodeState value134) :=
    JGm_TX2_View.value (s03 s) indices03 values03 4160 v03 4#usize (by decide)
  have active03 : 4#usize<(s03 s).n := by
    change (4:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=4160#usize := UScalar.eq_of_val_eq v03.at_eq
  have rn03 : Array.index_usize (s03 s).idx 5#usize=ok (22#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s03 s) indices03 values03 4160 v03 5#usize (by decide)
  have rr03 : Array.index_usize (s03 s).val 5#usize=ok (encodeState value135) :=
    JGm_TX2_View.value (s03 s) indices03 values03 4160 v03 5#usize (by decide)
  have selected03 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 3#usize 5#usize 6#usize 22#u32
    (encodeState value134) (encodeState value135) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (5:Nat)<(s03 s).n.val;rw [v03.size];decide)
    rn03 rr03 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 4#usize 3#usize=
        ok (.Next (s04 s) 6#usize 4#usize) := by
    rw [selected03]
    rw [cursor03]
    exact JHh_C_Gu_ParentCalls1.source142 D hash (s03 s) 6#usize 4160#usize 22#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 4160 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 4160 v03
      22#u32 3#usize (encodeState value142) 4160#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 6#usize=ok 25#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 4160 v04 6#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 6#usize=ok (encodeState value136) :=
    JGm_TX2_View.value (s04 s) indices04 values04 4160 v04 6#usize (by decide)
  have active04 : 6#usize<(s04 s).n := by
    change (6:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=4160#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 7#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 7#usize=ok other ∧ other≠25#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨26#u32,JGm_TX2_View.index (s04 s) indices04 values04 4160 v04 7#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 4192#usize)=ok (encodeState (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 6#usize 4#usize 7#usize 4192#usize 256#usize
    25#u32 (encodeState value136) (encodeState (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 25#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 6#usize 4#usize=
        ok (.Next (s05 s) 7#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source143 D hash (s04 s) 7#usize 4192#usize 25#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 4192 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 4160 v04
      25#u32 4#usize (encodeState value143) 4192#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 7#usize=ok 26#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 4192 v05 7#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 7#usize=ok (encodeState value137) :=
    JGm_TX2_View.value (s05 s) indices05 values05 4192 v05 7#usize (by decide)
  have active05 : 7#usize<(s05 s).n := by
    change (7:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=4192#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 8#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 8#usize=ok other ∧ other≠26#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨30#u32,JGm_TX2_View.index (s05 s) indices05 values05 4192 v05 8#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s05 s).«at» 4224#usize)=ok (encodeState (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes1 7#usize 5#usize 8#usize 4224#usize 224#usize
    26#u32 (encodeState value137) (encodeState (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read05
  simp only [show 26#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes1 7#usize 5#usize=
        ok (.Next (s06 s) 8#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls1.source144 D hash (s05 s) 8#usize 4224#usize 26#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 4224 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 4192 v05
      26#u32 5#usize (encodeState value144) 4224#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 8#usize=ok 30#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 4224 v06 8#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 8#usize=ok (encodeState value138) :=
    JGm_TX2_View.value (s06 s) indices06 values06 4224 v06 8#usize (by decide)
  have active06 : 8#usize<(s06 s).n := by
    change (8:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=4224#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 9#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 9#usize=ok other ∧ other≠30#u32 ^^^ 1#u32 := by
    intro more
    change (9:Nat)<(s06 s).n.val at more
    rw [v06.size] at more
    exact False.elim ((by decide : ¬(9:Nat)<9) more)
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s06 s).«at» 4256#usize)=ok (encodeState (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes1 8#usize 6#usize 9#usize 4256#usize 192#usize
    30#u32 (encodeState value138) (encodeState (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read06
  simp only [show 30#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes1 8#usize 6#usize=
        ok (.Next (s07 s) 9#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls1.source145 D hash (s06 s) 9#usize 4256#usize 30#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 4256 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 4224 v06
      30#u32 6#usize (encodeState value145) 4256#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes1 4#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes1 6#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes1 7#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes1 8#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes1 9#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s07 s).n.val≤9;rw [v07.size];decide)
  · exact JGm_TX2_View.finish (s07 s) indices07 values07 4256
      v07 7#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_13
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_14
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,13#u32,15#u32]
def values00 : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143,encodeState value144,encodeState value145]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 4#u32 0#usize (encodeState value146) 4256#usize
 def indices01 : List U32 := [2#u32,5#u32,9#u32,11#u32,12#u32,13#u32,15#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value146,encodeState value140,encodeState value141,encodeState value142,encodeState value143,encodeState value144,encodeState value145]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 9#u32 1#usize (encodeState value147) 4288#usize
 def indices02 : List U32 := [2#u32,4#u32,9#u32,11#u32,12#u32,13#u32,15#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value146,encodeState value147,encodeState value141,encodeState value142,encodeState value143,encodeState value144,encodeState value145]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 11#u32 2#usize (encodeState value148) 4320#usize
 def indices03 : List U32 := [2#u32,4#u32,5#u32,11#u32,12#u32,13#u32,15#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value146,encodeState value147,encodeState value148,encodeState value142,encodeState value143,encodeState value144,encodeState value145]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 12#u32 3#usize (encodeState value149) 4320#usize
 def indices04 : List U32 := [2#u32,4#u32,5#u32,6#u32,12#u32,13#u32,15#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value143,encodeState value144,encodeState value145]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 15#u32 4#usize (encodeState value150) 4352#usize
 def indices05 : List U32 := [2#u32,4#u32,5#u32,6#u32,7#u32,13#u32,15#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150,encodeState value144,encodeState value145]
def output (s : reference.Scratch) : reference.Scratch := {s05 s with n:=5#usize}
 def indicesOut : List U32 := [2#u32,4#u32,5#u32,6#u32,7#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150]
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      4256#usize 4288#usize)=ok (encodeState (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4256#usize 4288#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 4256#usize 4288#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 4256).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37287).take 32)=(encodeState (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 4256#usize 4288#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      4288#usize 4320#usize)=ok (encodeState (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4288#usize 4320#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 4288#usize 4320#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 4288).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37319).take 32)=(encodeState (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 4288#usize 4320#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      4320#usize 4352#usize)=ok (encodeState (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4320#usize 4352#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 4320#usize 4352#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 4320).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37351).take 32)=(encodeState (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 4320#usize 4352#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193])).property];decide)
  exact same ▸ run
#print axioms read04
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 4256) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 4352 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 4256 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 4#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 4256 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value139) :=
    JGm_TX2_View.value (s00 s) indices00 values00 4256 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=4256#usize := UScalar.eq_of_val_eq v00.at_eq
  have rn00 : Array.index_usize (s00 s).idx 1#usize=ok (4#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s00 s) indices00 values00 4256 v00 1#usize (by decide)
  have rr00 : Array.index_usize (s00 s).val 1#usize=ok (encodeState value140) :=
    JGm_TX2_View.value (s00 s) indices00 values00 4256 v00 1#usize (by decide)
  have selected00 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 2#usize 4#u32
    (encodeState value139) (encodeState value140) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (1:Nat)<(s00 s).n.val;rw [v00.size];decide)
    rn00 rr00 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 2#usize 1#usize) := by
    rw [selected00]
    rw [cursor00]
    exact JHh_C_Gu_ParentCalls1.source146 D hash (s00 s) 2#usize 4256#usize 4#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 4256 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 4256 v00
      4#u32 0#usize (encodeState value146) 4256#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 2#usize=ok 9#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 4256 v01 2#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 2#usize=ok (encodeState value141) :=
    JGm_TX2_View.value (s01 s) indices01 values01 4256 v01 2#usize (by decide)
  have active01 : 2#usize<(s01 s).n := by
    change (2:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=4256#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 3#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 3#usize=ok other ∧ other≠9#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨11#u32,JGm_TX2_View.index (s01 s) indices01 values01 4256 v01 3#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 4288#usize)=ok (encodeState (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 1#usize 3#usize 4288#usize 160#usize
    9#u32 (encodeState value141) (encodeState (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 9#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 2#usize 1#usize=
        ok (.Next (s02 s) 3#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source147 D hash (s01 s) 3#usize 4288#usize 9#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 4288 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 4256 v01
      9#u32 1#usize (encodeState value147) 4288#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 3#usize=ok 11#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 4288 v02 3#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 3#usize=ok (encodeState value142) :=
    JGm_TX2_View.value (s02 s) indices02 values02 4288 v02 3#usize (by decide)
  have active02 : 3#usize<(s02 s).n := by
    change (3:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=4288#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 4#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 4#usize=ok other ∧ other≠11#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨12#u32,JGm_TX2_View.index (s02 s) indices02 values02 4288 v02 4#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s02 s).«at» 4320#usize)=ok (encodeState (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 2#usize 4#usize 4320#usize 128#usize
    11#u32 (encodeState value142) (encodeState (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read02
  simp only [show 11#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 3#usize 2#usize=
        ok (.Next (s03 s) 4#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls1.source148 D hash (s02 s) 4#usize 4320#usize 11#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 4320 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 4288 v02
      11#u32 2#usize (encodeState value148) 4320#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 4#usize=ok 12#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 4320 v03 4#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 4#usize=ok (encodeState value143) :=
    JGm_TX2_View.value (s03 s) indices03 values03 4320 v03 4#usize (by decide)
  have active03 : 4#usize<(s03 s).n := by
    change (4:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=4320#usize := UScalar.eq_of_val_eq v03.at_eq
  have rn03 : Array.index_usize (s03 s).idx 5#usize=ok (12#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s03 s) indices03 values03 4320 v03 5#usize (by decide)
  have rr03 : Array.index_usize (s03 s).val 5#usize=ok (encodeState value144) :=
    JGm_TX2_View.value (s03 s) indices03 values03 4320 v03 5#usize (by decide)
  have selected03 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 3#usize 5#usize 6#usize 12#u32
    (encodeState value143) (encodeState value144) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (5:Nat)<(s03 s).n.val;rw [v03.size];decide)
    rn03 rr03 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 4#usize 3#usize=
        ok (.Next (s04 s) 6#usize 4#usize) := by
    rw [selected03]
    rw [cursor03]
    exact JHh_C_Gu_ParentCalls1.source149 D hash (s03 s) 6#usize 4320#usize 12#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 4320 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 4320 v03
      12#u32 3#usize (encodeState value149) 4320#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 6#usize=ok 15#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 4320 v04 6#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 6#usize=ok (encodeState value145) :=
    JGm_TX2_View.value (s04 s) indices04 values04 4320 v04 6#usize (by decide)
  have active04 : 6#usize<(s04 s).n := by
    change (6:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=4320#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 7#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 7#usize=ok other ∧ other≠15#u32 ^^^ 1#u32 := by
    intro more
    change (7:Nat)<(s04 s).n.val at more
    rw [v04.size] at more
    exact False.elim ((by decide : ¬(7:Nat)<7) more)
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 4352#usize)=ok (encodeState (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 6#usize 4#usize 7#usize 4352#usize 96#usize
    15#u32 (encodeState value145) (encodeState (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 15#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 6#usize 4#usize=
        ok (.Next (s05 s) 7#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source150 D hash (s04 s) 7#usize 4352#usize 15#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 4352 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 4320 v04
      15#u32 4#usize (encodeState value150) 4352#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes1 2#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes1 3#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes1 4#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes1 6#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes1 7#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s05 s).n.val≤7;rw [v05.size];decide)
  · exact JGm_TX2_View.finish (s05 s) indices05 values05 4352
      v05 5#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_14
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_15
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [2#u32,4#u32,5#u32,6#u32,7#u32]
def values00 : List (Array U8 32#usize) := [encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 2#u32 0#usize (encodeState value151) 4384#usize
 def indices01 : List U32 := [1#u32,4#u32,5#u32,6#u32,7#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value151,encodeState value147,encodeState value148,encodeState value149,encodeState value150]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 4#u32 1#usize (encodeState value152) 4384#usize
 def indices02 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value151,encodeState value152,encodeState value148,encodeState value149,encodeState value150]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 6#u32 2#usize (encodeState value153) 4384#usize
 def indices03 : List U32 := [1#u32,2#u32,3#u32,6#u32,7#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value151,encodeState value152,encodeState value153,encodeState value149,encodeState value150]
def output (s : reference.Scratch) : reference.Scratch := {s03 s with n:=3#usize}
 def indicesOut : List U32 := [1#u32,2#u32,3#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value151,encodeState value152,encodeState value153]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      4352#usize 4384#usize)=ok (encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4352#usize 4384#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 4352#usize 4384#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 4352).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37383).take 32)=(encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 4352#usize 4384#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160])).property];decide)
  exact same ▸ run
#print axioms read00
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 4352) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 4384 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 4352 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 2#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 4352 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value146) :=
    JGm_TX2_View.value (s00 s) indices00 values00 4352 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=4352#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠2#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨4#u32,JGm_TX2_View.index (s00 s) indices00 values00 4352 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 4384#usize)=ok (encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 4384#usize 64#usize
    2#u32 (encodeState value146) (encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 2#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source151 D hash (s00 s) 1#usize 4384#usize 2#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 4384 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 4352 v00
      2#u32 0#usize (encodeState value151) 4384#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 4#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 4384 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value147) :=
    JGm_TX2_View.value (s01 s) indices01 values01 4384 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=4384#usize := UScalar.eq_of_val_eq v01.at_eq
  have rn01 : Array.index_usize (s01 s).idx 2#usize=ok (4#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s01 s) indices01 values01 4384 v01 2#usize (by decide)
  have rr01 : Array.index_usize (s01 s).val 2#usize=ok (encodeState value148) :=
    JGm_TX2_View.value (s01 s) indices01 values01 4384 v01 2#usize (by decide)
  have selected01 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 3#usize 4#u32
    (encodeState value147) (encodeState value148) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (2:Nat)<(s01 s).n.val;rw [v01.size];decide)
    rn01 rr01 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 3#usize 2#usize) := by
    rw [selected01]
    rw [cursor01]
    exact JHh_C_Gu_ParentCalls1.source152 D hash (s01 s) 3#usize 4384#usize 4#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 4384 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 4384 v01
      4#u32 1#usize (encodeState value152) 4384#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 3#usize=ok 6#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 4384 v02 3#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 3#usize=ok (encodeState value149) :=
    JGm_TX2_View.value (s02 s) indices02 values02 4384 v02 3#usize (by decide)
  have active02 : 3#usize<(s02 s).n := by
    change (3:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=4384#usize := UScalar.eq_of_val_eq v02.at_eq
  have rn02 : Array.index_usize (s02 s).idx 4#usize=ok (6#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s02 s) indices02 values02 4384 v02 4#usize (by decide)
  have rr02 : Array.index_usize (s02 s).val 4#usize=ok (encodeState value150) :=
    JGm_TX2_View.value (s02 s) indices02 values02 4384 v02 4#usize (by decide)
  have selected02 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 2#usize 4#usize 5#usize 6#u32
    (encodeState value149) (encodeState value150) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (4:Nat)<(s02 s).n.val;rw [v02.size];decide)
    rn02 rr02 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 3#usize 2#usize=
        ok (.Next (s03 s) 5#usize 3#usize) := by
    rw [selected02]
    rw [cursor02]
    exact JHh_C_Gu_ParentCalls1.source153 D hash (s02 s) 5#usize 4384#usize 6#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 4384 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 4384 v02
      6#u32 2#usize (encodeState value153) 4384#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes1 3#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes1 5#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s03 s).n.val≤5;rw [v03.size];decide)
  · exact JGm_TX2_View.finish (s03 s) indices03 values03 4384
      v03 3#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_15
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_16
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [1#u32,2#u32,3#u32]
def values00 : List (Array U8 32#usize) := [encodeState value151,encodeState value152,encodeState value153]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 1#u32 0#usize (encodeState value154) 4416#usize
 def indices01 : List U32 := [0#u32,2#u32,3#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value154,encodeState value152,encodeState value153]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 2#u32 1#usize (encodeState value155) 4416#usize
 def indices02 : List U32 := [0#u32,1#u32,3#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value154,encodeState value155,encodeState value153]
def output (s : reference.Scratch) : reference.Scratch := {s02 s with n:=2#usize}
 def indicesOut : List U32 := [0#u32,1#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value154,encodeState value155]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      4384#usize 4416#usize)=ok (encodeState (JGc_TX2_HashBytes.state [141,210,29,143,172,113,121,140,232,80,9,198,209,48,160,240,216,160,117,117,21,164,211,65,104,173,187,170,81,120,182,252])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4384#usize 4416#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 4384#usize 4416#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [141,210,29,143,172,113,121,140,232,80,9,198,209,48,160,240,216,160,117,117,21,164,211,65,104,173,187,170,81,120,182,252])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 4384).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37415).take 32)=(encodeState (JGc_TX2_HashBytes.state [141,210,29,143,172,113,121,140,232,80,9,198,209,48,160,240,216,160,117,117,21,164,211,65,104,173,187,170,81,120,182,252])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 4384#usize 4416#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [141,210,29,143,172,113,121,140,232,80,9,198,209,48,160,240,216,160,117,117,21,164,211,65,104,173,187,170,81,120,182,252])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [141,210,29,143,172,113,121,140,232,80,9,198,209,48,160,240,216,160,117,117,21,164,211,65,104,173,187,170,81,120,182,252]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [141,210,29,143,172,113,121,140,232,80,9,198,209,48,160,240,216,160,117,117,21,164,211,65,104,173,187,170,81,120,182,252])).property];decide)
  exact same ▸ run
#print axioms read00
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 4384) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 4416 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 4384 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 1#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 4384 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value151) :=
    JGm_TX2_View.value (s00 s) indices00 values00 4384 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=4384#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠1#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2#u32,JGm_TX2_View.index (s00 s) indices00 values00 4384 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 4416#usize)=ok (encodeState (JGc_TX2_HashBytes.state [141,210,29,143,172,113,121,140,232,80,9,198,209,48,160,240,216,160,117,117,21,164,211,65,104,173,187,170,81,120,182,252])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 4416#usize 32#usize
    1#u32 (encodeState value151) (encodeState (JGc_TX2_HashBytes.state [141,210,29,143,172,113,121,140,232,80,9,198,209,48,160,240,216,160,117,117,21,164,211,65,104,173,187,170,81,120,182,252])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 1#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source154 D hash (s00 s) 1#usize 4416#usize 1#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 4416 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 4384 v00
      1#u32 0#usize (encodeState value154) 4416#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 2#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 4416 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value152) :=
    JGm_TX2_View.value (s01 s) indices01 values01 4416 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=4416#usize := UScalar.eq_of_val_eq v01.at_eq
  have rn01 : Array.index_usize (s01 s).idx 2#usize=ok (2#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s01 s) indices01 values01 4416 v01 2#usize (by decide)
  have rr01 : Array.index_usize (s01 s).val 2#usize=ok (encodeState value153) :=
    JGm_TX2_View.value (s01 s) indices01 values01 4416 v01 2#usize (by decide)
  have selected01 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 3#usize 2#u32
    (encodeState value152) (encodeState value153) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (2:Nat)<(s01 s).n.val;rw [v01.size];decide)
    rn01 rr01 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 3#usize 2#usize) := by
    rw [selected01]
    rw [cursor01]
    exact JHh_C_Gu_ParentCalls1.source155 D hash (s01 s) 3#usize 4416#usize 2#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 4416 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 4416 v01
      2#u32 1#usize (encodeState value155) 4416#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes1 3#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s02 s).n.val≤3;rw [v02.size];decide)
  · exact JGm_TX2_View.finish (s02 s) indices02 values02 4416
      v02 2#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_16
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_17
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [0#u32,1#u32]
def values00 : List (Array U8 32#usize) := [encodeState value154,encodeState value155]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 0#u32 0#usize (encodeState value156) 4416#usize
 def indices01 : List U32 := [0#u32,1#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value156,encodeState value155]
def output (s : reference.Scratch) : reference.Scratch := {s01 s with n:=1#usize}
 def indicesOut : List U32 := [0#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value156]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 4416) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 4416 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 4416 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 4416 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value154) :=
    JGm_TX2_View.value (s00 s) indices00 values00 4416 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=4416#usize := UScalar.eq_of_val_eq v00.at_eq
  have rn00 : Array.index_usize (s00 s).idx 1#usize=ok (0#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s00 s) indices00 values00 4416 v00 1#usize (by decide)
  have rr00 : Array.index_usize (s00 s).val 1#usize=ok (encodeState value155) :=
    JGm_TX2_View.value (s00 s) indices00 values00 4416 v00 1#usize (by decide)
  have selected00 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 2#usize 0#u32
    (encodeState value154) (encodeState value155) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (1:Nat)<(s00 s).n.val;rw [v00.size];decide)
    rn00 rr00 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 2#usize 1#usize) := by
    rw [selected00]
    rw [cursor00]
    exact JHh_C_Gu_ParentCalls1.source156 D hash (s00 s) 2#usize 4416#usize 0#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 4416 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 4416 v00
      0#u32 0#usize (encodeState value156) 4416#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes1 2#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s01 s).n.val≤2;rw [v01.size];decide)
  · exact JGm_TX2_View.finish (s01 s) indices01 values01 4416
      v01 1#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_17
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gu_Initial1
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
theorem idx01 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s01 s).idx.val.take 1=[65593#u32] := by
  change ((JHh_C_Gu_Scratch1.s00 s).idx.set (JHh_C_Gu_Scratch1.s00 s).n (65593#u32)).val.take 1=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s00 s).idx.val.set 0 (65593#u32)).take (0+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s00 s).idx.val.length=16 := (JHh_C_Gu_Scratch1.s00 s).idx.property
    omega)]
  rfl
#print axioms idx01
theorem idx02 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s02 s).idx.val.take 2=[65593#u32,93499#u32] := by
  change ((JHh_C_Gu_Scratch1.s01 s).idx.set (JHh_C_Gu_Scratch1.s01 s).n (93499#u32)).val.take 2=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s01 s).idx.val.set 1 (93499#u32)).take (1+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s01 s).idx.val.length=16 := (JHh_C_Gu_Scratch1.s01 s).idx.property
    omega)]
  rw [idx01]
  rfl
#print axioms idx02
theorem idx03 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s03 s).idx.val.take 3=[65593#u32,93499#u32,147529#u32] := by
  change ((JHh_C_Gu_Scratch1.s02 s).idx.set (JHh_C_Gu_Scratch1.s02 s).n (147529#u32)).val.take 3=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s02 s).idx.val.set 2 (147529#u32)).take (2+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s02 s).idx.val.length=16 := (JHh_C_Gu_Scratch1.s02 s).idx.property
    omega)]
  rw [idx02]
  rfl
#print axioms idx03
theorem idx04 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s04 s).idx.val.take 4=[65593#u32,93499#u32,147529#u32,159813#u32] := by
  change ((JHh_C_Gu_Scratch1.s03 s).idx.set (JHh_C_Gu_Scratch1.s03 s).n (159813#u32)).val.take 4=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s03 s).idx.val.set 3 (159813#u32)).take (3+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s03 s).idx.val.length=16 := (JHh_C_Gu_Scratch1.s03 s).idx.property
    omega)]
  rw [idx03]
  rfl
#print axioms idx04
theorem idx05 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s05 s).idx.val.take 5=[65593#u32,93499#u32,147529#u32,159813#u32,183859#u32] := by
  change ((JHh_C_Gu_Scratch1.s04 s).idx.set (JHh_C_Gu_Scratch1.s04 s).n (183859#u32)).val.take 5=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s04 s).idx.val.set 4 (183859#u32)).take (4+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s04 s).idx.val.length=16 := (JHh_C_Gu_Scratch1.s04 s).idx.property
    omega)]
  rw [idx04]
  rfl
#print axioms idx05
theorem idx06 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s06 s).idx.val.take 6=[65593#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32] := by
  change ((JHh_C_Gu_Scratch1.s05 s).idx.set (JHh_C_Gu_Scratch1.s05 s).n (192317#u32)).val.take 6=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s05 s).idx.val.set 5 (192317#u32)).take (5+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s05 s).idx.val.length=16 := (JHh_C_Gu_Scratch1.s05 s).idx.property
    omega)]
  rw [idx05]
  rfl
#print axioms idx06
theorem idx07 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s07 s).idx.val.take 7=[65593#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32] := by
  change ((JHh_C_Gu_Scratch1.s06 s).idx.set (JHh_C_Gu_Scratch1.s06 s).n (193093#u32)).val.take 7=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s06 s).idx.val.set 6 (193093#u32)).take (6+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s06 s).idx.val.length=16 := (JHh_C_Gu_Scratch1.s06 s).idx.property
    omega)]
  rw [idx06]
  rfl
#print axioms idx07
theorem idx08 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s08 s).idx.val.take 8=[65593#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32] := by
  change ((JHh_C_Gu_Scratch1.s07 s).idx.set (JHh_C_Gu_Scratch1.s07 s).n (209371#u32)).val.take 8=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s07 s).idx.val.set 7 (209371#u32)).take (7+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s07 s).idx.val.length=16 := (JHh_C_Gu_Scratch1.s07 s).idx.property
    omega)]
  rw [idx07]
  rfl
#print axioms idx08
theorem idx09 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s09 s).idx.val.take 9=[65593#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32] := by
  change ((JHh_C_Gu_Scratch1.s08 s).idx.set (JHh_C_Gu_Scratch1.s08 s).n (216823#u32)).val.take 9=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s08 s).idx.val.set 8 (216823#u32)).take (8+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s08 s).idx.val.length=16 := (JHh_C_Gu_Scratch1.s08 s).idx.property
    omega)]
  rw [idx08]
  rfl
#print axioms idx09
theorem idx10 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s10 s).idx.val.take 10=[65593#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32] := by
  change ((JHh_C_Gu_Scratch1.s09 s).idx.set (JHh_C_Gu_Scratch1.s09 s).n (245899#u32)).val.take 10=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s09 s).idx.val.set 9 (245899#u32)).take (9+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s09 s).idx.val.length=16 := (JHh_C_Gu_Scratch1.s09 s).idx.property
    omega)]
  rw [idx09]
  rfl
#print axioms idx10
theorem val01 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s01 s).val.val.take 1=[encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩)] := by
  change ((JHh_C_Gu_Scratch1.s00 s).val.set (JHh_C_Gu_Scratch1.s00 s).n (encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩))).val.take 1=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s00 s).val.val.set 0 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩))).take (0+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s00 s).val.val.length=16 := (JHh_C_Gu_Scratch1.s00 s).val.property
    omega)]
  rfl
#print axioms val01
theorem val02 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s02 s).val.val.take 2=[encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨0,by decide⟩)] := by
  change ((JHh_C_Gu_Scratch1.s01 s).val.set (JHh_C_Gu_Scratch1.s01 s).n (encodeState (JHh_C_Gu_LeafIteration1.value ⟨0,by decide⟩))).val.take 2=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s01 s).val.val.set 1 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨0,by decide⟩))).take (1+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s01 s).val.val.length=16 := (JHh_C_Gu_Scratch1.s01 s).val.property
    omega)]
  rw [val01]
  rfl
#print axioms val02
theorem val03 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s03 s).val.val.take 3=[encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨0,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨1,by decide⟩)] := by
  change ((JHh_C_Gu_Scratch1.s02 s).val.set (JHh_C_Gu_Scratch1.s02 s).n (encodeState (JHh_C_Gu_LeafIteration1.value ⟨1,by decide⟩))).val.take 3=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s02 s).val.val.set 2 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨1,by decide⟩))).take (2+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s02 s).val.val.length=16 := (JHh_C_Gu_Scratch1.s02 s).val.property
    omega)]
  rw [val02]
  rfl
#print axioms val03
theorem val04 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s04 s).val.val.take 4=[encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨0,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨1,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨9,by decide⟩)] := by
  change ((JHh_C_Gu_Scratch1.s03 s).val.set (JHh_C_Gu_Scratch1.s03 s).n (encodeState (JHh_C_Gu_LeafIteration1.value ⟨9,by decide⟩))).val.take 4=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s03 s).val.val.set 3 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨9,by decide⟩))).take (3+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s03 s).val.val.length=16 := (JHh_C_Gu_Scratch1.s03 s).val.property
    omega)]
  rw [val03]
  rfl
#print axioms val04
theorem val05 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s05 s).val.val.take 5=[encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨0,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨1,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨9,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨7,by decide⟩)] := by
  change ((JHh_C_Gu_Scratch1.s04 s).val.set (JHh_C_Gu_Scratch1.s04 s).n (encodeState (JHh_C_Gu_LeafIteration1.value ⟨7,by decide⟩))).val.take 5=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s04 s).val.val.set 4 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨7,by decide⟩))).take (4+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s04 s).val.val.length=16 := (JHh_C_Gu_Scratch1.s04 s).val.property
    omega)]
  rw [val04]
  rfl
#print axioms val05
theorem val06 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s06 s).val.val.take 6=[encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨0,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨1,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨9,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨7,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨5,by decide⟩)] := by
  change ((JHh_C_Gu_Scratch1.s05 s).val.set (JHh_C_Gu_Scratch1.s05 s).n (encodeState (JHh_C_Gu_LeafIteration1.value ⟨5,by decide⟩))).val.take 6=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s05 s).val.val.set 5 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨5,by decide⟩))).take (5+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s05 s).val.val.length=16 := (JHh_C_Gu_Scratch1.s05 s).val.property
    omega)]
  rw [val05]
  rfl
#print axioms val06
theorem val07 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s07 s).val.val.take 7=[encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨0,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨1,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨9,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨7,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨5,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨8,by decide⟩)] := by
  change ((JHh_C_Gu_Scratch1.s06 s).val.set (JHh_C_Gu_Scratch1.s06 s).n (encodeState (JHh_C_Gu_LeafIteration1.value ⟨8,by decide⟩))).val.take 7=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s06 s).val.val.set 6 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨8,by decide⟩))).take (6+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s06 s).val.val.length=16 := (JHh_C_Gu_Scratch1.s06 s).val.property
    omega)]
  rw [val06]
  rfl
#print axioms val07
theorem val08 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s08 s).val.val.take 8=[encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨0,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨1,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨9,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨7,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨5,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨8,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨4,by decide⟩)] := by
  change ((JHh_C_Gu_Scratch1.s07 s).val.set (JHh_C_Gu_Scratch1.s07 s).n (encodeState (JHh_C_Gu_LeafIteration1.value ⟨4,by decide⟩))).val.take 8=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s07 s).val.val.set 7 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨4,by decide⟩))).take (7+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s07 s).val.val.length=16 := (JHh_C_Gu_Scratch1.s07 s).val.property
    omega)]
  rw [val07]
  rfl
#print axioms val08
theorem val09 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s09 s).val.val.take 9=[encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨0,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨1,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨9,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨7,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨5,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨8,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨4,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨2,by decide⟩)] := by
  change ((JHh_C_Gu_Scratch1.s08 s).val.set (JHh_C_Gu_Scratch1.s08 s).n (encodeState (JHh_C_Gu_LeafIteration1.value ⟨2,by decide⟩))).val.take 9=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s08 s).val.val.set 8 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨2,by decide⟩))).take (8+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s08 s).val.val.length=16 := (JHh_C_Gu_Scratch1.s08 s).val.property
    omega)]
  rw [val08]
  rfl
#print axioms val09
theorem val10 (s : reference.Scratch) :
    (JHh_C_Gu_Scratch1.s10 s).val.val.take 10=[encodeState (JHh_C_Gu_LeafIteration1.value ⟨6,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨0,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨1,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨9,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨7,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨5,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨8,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨4,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨2,by decide⟩),encodeState (JHh_C_Gu_LeafIteration1.value ⟨3,by decide⟩)] := by
  change ((JHh_C_Gu_Scratch1.s09 s).val.set (JHh_C_Gu_Scratch1.s09 s).n (encodeState (JHh_C_Gu_LeafIteration1.value ⟨3,by decide⟩))).val.take 10=_
  rw [Array.set_val_eq]
  change ((JHh_C_Gu_Scratch1.s09 s).val.val.set 9 (encodeState (JHh_C_Gu_LeafIteration1.value ⟨3,by decide⟩))).take (9+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHh_C_Gu_Scratch1.s09 s).val.val.length=16 := (JHh_C_Gu_Scratch1.s09 s).val.property
    omega)]
  rw [val09]
  rfl
#print axioms val10
theorem source (s : reference.Scratch) :
    JGm_TX2_View.View (JHh_C_Gu_Scratch1.s10 s) JHh_C_Gu_Level1_00.indices00 JHh_C_Gu_Level1_00.values00 0 := by
  refine ⟨rfl,rfl,?_,?_,rfl⟩
  · exact idx10 s
  · exact val10 s
#print axioms source
end AspisR1.JHh_C_Gu_Initial1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gu_Levels1
open Aeneas Aeneas.Std Result MultiproofConeRef

def PhaseView (height : Nat) (s : reference.Scratch) : Prop := match height with
  | 0 => JGm_TX2_View.View s JHh_C_Gu_Level1_00.indices00 JHh_C_Gu_Level1_00.values00 0
  | 1 => JGm_TX2_View.View s JHh_C_Gu_Level1_01.indices00 JHh_C_Gu_Level1_01.values00 320
  | 2 => JGm_TX2_View.View s JHh_C_Gu_Level1_02.indices00 JHh_C_Gu_Level1_02.values00 640
  | 3 => JGm_TX2_View.View s JHh_C_Gu_Level1_03.indices00 JHh_C_Gu_Level1_03.values00 960
  | 4 => JGm_TX2_View.View s JHh_C_Gu_Level1_04.indices00 JHh_C_Gu_Level1_04.values00 1280
  | 5 => JGm_TX2_View.View s JHh_C_Gu_Level1_05.indices00 JHh_C_Gu_Level1_05.values00 1600
  | 6 => JGm_TX2_View.View s JHh_C_Gu_Level1_06.indices00 JHh_C_Gu_Level1_06.values00 1920
  | 7 => JGm_TX2_View.View s JHh_C_Gu_Level1_07.indices00 JHh_C_Gu_Level1_07.values00 2240
  | 8 => JGm_TX2_View.View s JHh_C_Gu_Level1_08.indices00 JHh_C_Gu_Level1_08.values00 2560
  | 9 => JGm_TX2_View.View s JHh_C_Gu_Level1_09.indices00 JHh_C_Gu_Level1_09.values00 2880
  | 10 => JGm_TX2_View.View s JHh_C_Gu_Level1_10.indices00 JHh_C_Gu_Level1_10.values00 3200
  | 11 => JGm_TX2_View.View s JHh_C_Gu_Level1_11.indices00 JHh_C_Gu_Level1_11.values00 3520
  | 12 => JGm_TX2_View.View s JHh_C_Gu_Level1_12.indices00 JHh_C_Gu_Level1_12.values00 3840
  | 13 => JGm_TX2_View.View s JHh_C_Gu_Level1_13.indices00 JHh_C_Gu_Level1_13.values00 4096
  | 14 => JGm_TX2_View.View s JHh_C_Gu_Level1_14.indices00 JHh_C_Gu_Level1_14.values00 4256
  | 15 => JGm_TX2_View.View s JHh_C_Gu_Level1_15.indices00 JHh_C_Gu_Level1_15.values00 4352
  | 16 => JGm_TX2_View.View s JHh_C_Gu_Level1_16.indices00 JHh_C_Gu_Level1_16.values00 4384
  | 17 => JGm_TX2_View.View s JHh_C_Gu_Level1_17.indices00 JHh_C_Gu_Level1_17.values00 4416
  | 18 => JGm_TX2_View.View s JHh_C_Gu_Level1_17.indicesOut JHh_C_Gu_Level1_17.valuesOut 4416
  | _ => False

theorem step {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (h : Nat) (bound : h<18) (s : reference.Scratch) (view : PhaseView h s) :
    ∃ out, reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash s
      JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done out) ∧ PhaseView (h+1) out := by
  interval_cases h
  · exact ⟨_,JHh_C_Gu_Level1_00.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_01.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_02.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_03.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_04.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_05.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_06.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_07.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_08.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_09.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_10.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_11.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_12.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_13.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_14.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_15.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_16.source D hash s view⟩
  · exact ⟨_,JHh_C_Gu_Level1_17.source D hash s view⟩
#print axioms step

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch)
    (view : JGm_TX2_View.View s JHh_C_Gu_Level1_00.indices00 JHh_C_Gu_Level1_00.values00 0) :
    ∃ out, reference.levels (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash s
      JGy_G_JGu_Supplied.nodes1 18#u32=ok (.Done out) ∧
    JGm_TX2_View.View out JHh_C_Gu_Level1_17.indicesOut JHh_C_Gu_Level1_17.valuesOut 4416 := by
  obtain ⟨out,run,last⟩ := JGm_TX2_HeightTools.compose (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash state JGy_G_JGu_Supplied.nodes1 0#usize 0#usize) 18 PhaseView (step D hash) s view
  refine ⟨out,?_,last⟩
  rw [MultiproofConeLevelIteration.levels_eq_iteration _ _ _ _ (by decide)]
  exact run
#print axioms source

theorem on_scratch {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    ∃ out, reference.levels (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (JHh_C_Gu_Scratch1.s10 s) JGy_G_JGu_Supplied.nodes1 18#u32=ok (.Done out) ∧
    JGm_TX2_View.View out JHh_C_Gu_Level1_17.indicesOut JHh_C_Gu_Level1_17.valuesOut 4416 :=
  source D hash _ (JHh_C_Gu_Initial1.source s)
#print axioms on_scratch
end AspisR1.JHh_C_Gu_Levels1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gu_Valid1
open Aeneas Aeneas.Std Result MultiproofConeRef
 theorem source (s : reference.Scratch)
    (view : JGm_TX2_View.View s JHh_C_Gu_Level1_00.indices00 JHh_C_Gu_Level1_00.values00 0) :
    reference.valid_indices s.idx 10#usize 0#usize=ok true := by
  have r00 : Array.index_usize s.idx 0#usize=ok 65593#u32 :=
    JGm_TX2_View.index s JHh_C_Gu_Level1_00.indices00 JHh_C_Gu_Level1_00.values00 0 view 0#usize (by decide)
  have r01 : Array.index_usize s.idx 1#usize=ok 93499#u32 :=
    JGm_TX2_View.index s JHh_C_Gu_Level1_00.indices00 JHh_C_Gu_Level1_00.values00 0 view 1#usize (by decide)
  have r02 : Array.index_usize s.idx 2#usize=ok 147529#u32 :=
    JGm_TX2_View.index s JHh_C_Gu_Level1_00.indices00 JHh_C_Gu_Level1_00.values00 0 view 2#usize (by decide)
  have r03 : Array.index_usize s.idx 3#usize=ok 159813#u32 :=
    JGm_TX2_View.index s JHh_C_Gu_Level1_00.indices00 JHh_C_Gu_Level1_00.values00 0 view 3#usize (by decide)
  have r04 : Array.index_usize s.idx 4#usize=ok 183859#u32 :=
    JGm_TX2_View.index s JHh_C_Gu_Level1_00.indices00 JHh_C_Gu_Level1_00.values00 0 view 4#usize (by decide)
  have r05 : Array.index_usize s.idx 5#usize=ok 192317#u32 :=
    JGm_TX2_View.index s JHh_C_Gu_Level1_00.indices00 JHh_C_Gu_Level1_00.values00 0 view 5#usize (by decide)
  have r06 : Array.index_usize s.idx 6#usize=ok 193093#u32 :=
    JGm_TX2_View.index s JHh_C_Gu_Level1_00.indices00 JHh_C_Gu_Level1_00.values00 0 view 6#usize (by decide)
  have r07 : Array.index_usize s.idx 7#usize=ok 209371#u32 :=
    JGm_TX2_View.index s JHh_C_Gu_Level1_00.indices00 JHh_C_Gu_Level1_00.values00 0 view 7#usize (by decide)
  have r08 : Array.index_usize s.idx 8#usize=ok 216823#u32 :=
    JGm_TX2_View.index s JHh_C_Gu_Level1_00.indices00 JHh_C_Gu_Level1_00.values00 0 view 8#usize (by decide)
  have r09 : Array.index_usize s.idx 9#usize=ok 245899#u32 :=
    JGm_TX2_View.index s JHh_C_Gu_Level1_00.indices00 JHh_C_Gu_Level1_00.values00 0 view 9#usize (by decide)
  calc
    reference.valid_indices s.idx 10#usize 0#usize=reference.valid_indices s.idx 10#usize 1#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬0#usize≥10#usize),r00]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬65593#u32≥262144#u32)]
      rw [if_neg (by decide : ¬0#usize>0#usize)]
      rw [JGy_G_JGm_TX2_Scalar.add 0#usize 1#usize 1#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 2#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬1#usize≥10#usize),r01]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬93499#u32≥262144#u32)]
      rw [if_pos (by decide : 1#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 1#usize 1#usize 0#usize (by decide) rfl,bind_tc_ok,r00,bind_tc_ok,
        if_neg (by decide : ¬65593#u32≥93499#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 1#usize 1#usize 2#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 3#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬2#usize≥10#usize),r02]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬147529#u32≥262144#u32)]
      rw [if_pos (by decide : 2#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 2#usize 1#usize 1#usize (by decide) rfl,bind_tc_ok,r01,bind_tc_ok,
        if_neg (by decide : ¬93499#u32≥147529#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 2#usize 1#usize 3#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 4#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬3#usize≥10#usize),r03]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬159813#u32≥262144#u32)]
      rw [if_pos (by decide : 3#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 3#usize 1#usize 2#usize (by decide) rfl,bind_tc_ok,r02,bind_tc_ok,
        if_neg (by decide : ¬147529#u32≥159813#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 3#usize 1#usize 4#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 5#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬4#usize≥10#usize),r04]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬183859#u32≥262144#u32)]
      rw [if_pos (by decide : 4#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 4#usize 1#usize 3#usize (by decide) rfl,bind_tc_ok,r03,bind_tc_ok,
        if_neg (by decide : ¬159813#u32≥183859#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 4#usize 1#usize 5#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 6#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬5#usize≥10#usize),r05]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬192317#u32≥262144#u32)]
      rw [if_pos (by decide : 5#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 5#usize 1#usize 4#usize (by decide) rfl,bind_tc_ok,r04,bind_tc_ok,
        if_neg (by decide : ¬183859#u32≥192317#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 5#usize 1#usize 6#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 7#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬6#usize≥10#usize),r06]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬193093#u32≥262144#u32)]
      rw [if_pos (by decide : 6#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 6#usize 1#usize 5#usize (by decide) rfl,bind_tc_ok,r05,bind_tc_ok,
        if_neg (by decide : ¬192317#u32≥193093#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 6#usize 1#usize 7#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 8#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬7#usize≥10#usize),r07]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬209371#u32≥262144#u32)]
      rw [if_pos (by decide : 7#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 7#usize 1#usize 6#usize (by decide) rfl,bind_tc_ok,r06,bind_tc_ok,
        if_neg (by decide : ¬193093#u32≥209371#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 7#usize 1#usize 8#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 9#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬8#usize≥10#usize),r08]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬216823#u32≥262144#u32)]
      rw [if_pos (by decide : 8#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 8#usize 1#usize 7#usize (by decide) rfl,bind_tc_ok,r07,bind_tc_ok,
        if_neg (by decide : ¬209371#u32≥216823#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 8#usize 1#usize 9#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 10#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬9#usize≥10#usize),r09]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬245899#u32≥262144#u32)]
      rw [if_pos (by decide : 9#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 9#usize 1#usize 8#usize (by decide) rfl,bind_tc_ok,r08,bind_tc_ok,
        if_neg (by decide : ¬216823#u32≥245899#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 9#usize 1#usize 10#usize rfl]
      rfl
    _=ok true := by rw [reference.valid_indices,if_pos (by decide : 10#usize≥10#usize)]
#print axioms source
theorem on_scratch (s : reference.Scratch) :
    reference.valid_indices (JHh_C_Gu_Scratch1.s10 s).idx 10#usize 0#usize=ok true :=
  source _ (JHh_C_Gu_Initial1.source s)
#print axioms on_scratch
end AspisR1.JHh_C_Gu_Valid1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gu_Verify1
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes0 JGy_G_JGu_Supplied.nodes1 JGy_G_JGu_Supplied.nodes2

def output {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) (s : reference.Scratch) : reference.Scratch := Classical.choose (JHh_C_Gu_Levels1.on_scratch D hash s)

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    reference.verify_owned (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (encodeState JHh_C_Gr_M1Root.retainedRoot) (JHh_C_Gu_Scratch1.s10 s) JGy_G_JGu_Supplied.nodes1=
        ok (true,output D hash s) := by
  obtain ⟨levels,view⟩ := Classical.choose_spec (JHh_C_Gu_Levels1.on_scratch D hash s)
  have n : (output D hash s).n=1#usize := UScalar.eq_of_val_eq view.size
  have at_eq : (output D hash s).«at»=4416#usize := UScalar.eq_of_val_eq view.at_eq
  have index : Array.index_usize (output D hash s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index _ _ _ _ view 0#usize (by decide)
  have value : Array.index_usize (output D hash s).val 0#usize=ok (encodeState JHh_C_Gr_M1Roots.value156) :=
    JGm_TX2_View.value _ _ _ _ view 0#usize (by decide)
  rw [JHh_C_Gr_M1Root.value_eq] at value
  have reset : {JHh_C_Gu_Scratch1.s10 s with «at»:=0#usize}=JHh_C_Gu_Scratch1.s10 s := rfl
  have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
  have modulo : 4416#usize % 32#usize=ok 0#usize := by
    obtain ⟨v,run,hv⟩ := WP.spec_imp_exists (UScalar.rem_spec (x:=4416#usize) (y:=32#usize) (by scalar_tac))
    have same : v=0#usize := UScalar.eq_of_val_eq (by simpa using hv)
    simpa only [same] using run
  have valid : reference.valid_indices (JHh_C_Gu_Scratch1.s10 s).idx (JHh_C_Gu_Scratch1.s10 s).n 0#usize=ok true := JHh_C_Gu_Valid1.on_scratch s
  rw [reference.verify_owned,
    if_neg (by change ¬10#usize=0#usize;decide),
    if_neg (by change ¬10#usize>16#usize;decide),valid]
  simp only [bind_tc_ok,Bool.true_eq,if_true,len,modulo,
    show (0#usize!=0#usize)=false from rfl,Bool.false_eq_true,if_false]
  rw [reset,levels]
  simp only [bind_tc_ok]
  change (do if (output D hash s).n=1#usize then
               let i ← Array.index_usize (output D hash s).idx 0#usize
               if i=0#u32 then
                 let a ← Array.index_usize (output D hash s).val 0#usize
                 let b ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a (encodeState JHh_C_Gr_M1Root.retainedRoot)
                 if b then ok (decide ((output D hash s).«at»=4416#usize),output D hash s)
                 else ok (false,output D hash s)
               else ok (false,output D hash s)
             else ok (false,output D hash s))=_
  simp only [n,if_pos rfl,index,value,bind_tc_ok,MultiproofConeLeaf.digest_eq_total,decide_true,
    Bool.true_eq,if_true,at_eq,len]
#print axioms source
end AspisR1.JHh_C_Gu_Verify1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gw_Terminal1
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGp_Slot1.value

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JHh_C_Gr_M1Root.retainedRoot) 1#usize hash
      0#usize 10#usize 1#usize (JGu_Keys.keys 1)
      (JHh_C_Gu_Scratch1.s10 s).idx (JHh_C_Gu_Scratch1.s10 s).val 10#usize 10#usize=
        ok (.done ((JHh_C_Gu_Verify1.output D hash s).idx,(JHh_C_Gu_Verify1.output D hash s).val,some (.Ok ()))) := by
  have frontRead : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      (JHh_C_Gu_Scratch1.s10 s).idx {«end»:=10#usize}=ok JGr_Count0.frontier := by
    simp only [Array.index_SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index]
    rw [if_pos (by change (10:Nat)≤(JHh_C_Gu_Scratch1.s10 s).idx.val.length;rw [(JHh_C_Gu_Scratch1.s10 s).idx.property];decide)]
    apply congrArg ok
    apply Subtype.ext
    exact JHh_C_Gu_Initial1.idx10 s
  have mul : Usize.wrapping_mul 32#usize 138#usize=4416#usize := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_mul_val_eq]
    apply Nat.mod_eq_of_lt
    rw [UScalar.size_def]
    scalar_tac
  have fits : (4416#usize).val≤JGp_Slot1.value.val.length := by
    have len : JGp_Slot1.value.val.length=4672 := JGp_Slot1.length
    rw [len]
    decide
  have drop : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      JGp_Slot1.value {start:=4416#usize}=ok JGy_G_JGu_Padding1.padding :=
    MultiproofConeSlices.drop_total _ _ fits
  have prefixRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      JGp_Slot1.value {«end»:=4416#usize}=ok JGy_G_JGu_Supplied.nodes1 :=
    MultiproofConeSlices.prefix_total _ _ fits
  obtain ⟨ce,after,chunks,scan⟩ := JGy_G_JGu_PaddingScan.calls (JGy_G_JGc_TX2_RealLeaves.dictionary D)
    JGy_G_JGu_Padding1.padding JGy_G_JGu_Padding1.bytes
  simp only [Port3_BatchStd.install] at scan
  have verify : Port4B_Install.leaves.op10 (JGy_G_JGc_TX2_RealLeaves.dictionary D) hash .Two
      (encodeState JHh_C_Gr_M1Root.retainedRoot)
      (JHh_C_Gu_Scratch1.s10 s).idx (JHh_C_Gu_Scratch1.s10 s).val 10#usize JGy_G_JGu_Supplied.nodes1=
      ok (true,(JHh_C_Gu_Verify1.output D hash s).idx,(JHh_C_Gu_Verify1.output D hash s).val) := by
    change (do
      let (b,out) ← reference.verify_owned
        (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
        (encodeState JHh_C_Gr_M1Root.retainedRoot) (JHh_C_Gu_Scratch1.s10 s) JGy_G_JGu_Supplied.nodes1
      ok (b,out.idx,out.val))=_
    rw [JHh_C_Gu_Verify1.source D hash s]
    rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body,
    if_neg (by decide : ¬10#usize<10#usize),frontRead]
  have countRead := JGr_Count0.source
  have nodeRead := JGp_Slot1.source
  change Port4B_Install.leaves.op3 JFx_NativeBytes.proof 1#usize=ok JGp_Slot1.value at nodeRead
  change Port4B_Install.leaves.op11 .Two _=_ at countRead
  simp only [bind_tc_ok,Port3_BatchStd.install,countRead,Port3_BatchStd.okOr,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [nodeRead]
  simp only [bind_tc_ok]
  have capacity : Array.index_usize
      (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize])
      1#usize=ok 146#usize := rfl
  rw [capacity]
  simp only [bind_tc_ok,show ¬138#usize>146#usize from by decide,if_false,
    mul,lift,drop,chunks,scan,prefixRead,verify,Bool.false_eq_true,Bool.true_eq,if_true]
  all_goals rfl
#print axioms source

theorem loop {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JHh_C_Gr_M1Root.retainedRoot) 1#usize
      (JHh_C_Gu_Scratch1.s00 s).idx (JHh_C_Gu_Scratch1.s00 s).val hash 0#usize 10#usize 1#usize
      (JGu_Keys.keys 1) 0#usize 0#usize=
        ok ((JHh_C_Gu_Verify1.output D hash s).idx,(JHh_C_Gu_Verify1.output D hash s).val,some (.Ok ())) := by
  apply (JHh_C_Gu_Scratch1.source D hash (encodeState JHh_C_Gr_M1Root.retainedRoot) s).trans
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JHh_C_Gr_M1Root.retainedRoot) 1#usize
      (JHh_C_Gu_Scratch1.s10 s).idx (JHh_C_Gu_Scratch1.s10 s).val hash 0#usize 10#usize 1#usize
      (JGu_Keys.keys 1) 10#usize 10#usize=_
  conv_lhs =>
    unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
    rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,source,bind_tc_ok]
#print axioms loop

end AspisR1.JHh_C_Gw_Terminal1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_Gw_Tree1
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGp_Slot1.value

theorem tree {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState JHh_C_Gr_M1Root.retainedRoot)
      0#usize 1#usize s.idx s.val hash=
        ok (.Ok (), (JHh_C_Gu_Verify1.output D hash s).idx,(JHh_C_Gu_Verify1.output D hash s).val) := by
  have splitCount : Usize.wrapping_sub 10#usize 0#usize=10#usize :=
    JHh_SmallConstants.count0
  have slot : Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) 1#usize=1#usize :=
    JHh_SmallConstants.slot1
  have hi : (Port3_BatchStd.install Port4B_Install.leaves).op13=ok 10#usize := rfl
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree
  have bounds : (if (0#usize : Usize)=0#usize then do
      let i ← (Port3_BatchStd.install Port4B_Install.leaves).op13
      ok (0#usize,i)
    else do
      let i ← (Port3_BatchStd.install Port4B_Install.leaves).op13
      ok (i,22#usize))=ok (0#usize,10#usize) := by
    rw [if_pos rfl,hi]
    rfl
  rw [bounds]
  change (do
    let a ← (Port3_BatchStd.install Port4B_Install.leaves).op4 JFo_Prepared.value.queries
      0#usize (Usize.wrapping_sub 10#usize 0#usize) 1#usize
    let keys ← (Port3_BatchStd.install Port4B_Install.leaves).op5 a (Usize.wrapping_sub 10#usize 0#usize)
    let (idx,val,pending) ← Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JHh_C_Gr_M1Root.retainedRoot) 1#usize
      s.idx s.val hash 0#usize (Usize.wrapping_sub 10#usize 0#usize) (Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) 1#usize) keys 0#usize 0#usize
    match pending with
    | none => fail .panic
    | some r => ok (r,idx,val))=_
  rw [splitCount,slot]
  have build : (Port3_BatchStd.install Port4B_Install.leaves).op4 JFo_Prepared.value.queries
      0#usize 10#usize 1#usize=ok (JGr_Keys.raw 1) := JGr_Keys.build 1#usize (by decide)
  have sort : (Port3_BatchStd.install Port4B_Install.leaves).op5 (JGr_Keys.raw 1) 10#usize=
      ok (JGu_Keys.keys 1) := JGu_Keys.returned 1
  rw [build,bind_tc_ok,sort,bind_tc_ok]
  have run := JHh_C_Gw_Terminal1.loop D hash s
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JHh_C_Gr_M1Root.retainedRoot) 1#usize
      s.idx s.val hash 0#usize 10#usize 1#usize (JGu_Keys.keys 1) 0#usize 0#usize=_ at run
  rw [run]
  rfl
#print axioms tree
end AspisR1.JHh_C_Gw_Tree1
end

end
