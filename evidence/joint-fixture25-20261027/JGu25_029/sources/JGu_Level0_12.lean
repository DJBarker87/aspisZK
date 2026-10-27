import JGu_ParentCalls0
import JGm_TX2_View
import JGm_TX2_RowControl
import JGm_TX2_ExternalRun
import JGu_Supplied
import JGk_TX2_SiblingLaws
import JFw_Frames
import JFq_Range
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JGu_Level0_12
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGr_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGu_Supplied.nodes0
def indices00 : List U32 := [16#u32,22#u32,36#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
def values00 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 16#u32 0#usize (encodeState value130) 3872#usize
 def indices01 : List U32 := [8#u32,22#u32,36#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value130,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 22#u32 1#usize (encodeState value131) 3904#usize
 def indices02 : List U32 := [8#u32,11#u32,36#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 36#u32 2#usize (encodeState value132) 3936#usize
 def indices03 : List U32 := [8#u32,11#u32,18#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 39#u32 3#usize (encodeState value133) 3968#usize
 def indices04 : List U32 := [8#u32,11#u32,18#u32,19#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 44#u32 4#usize (encodeState value134) 4000#usize
 def indices05 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 46#u32 5#usize (encodeState value135) 4000#usize
 def indices06 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,47#u32,51#u32,52#u32,60#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 51#u32 6#usize (encodeState value136) 4032#usize
 def indices07 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,51#u32,52#u32,60#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value127,encodeState value128,encodeState value129]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 52#u32 7#usize (encodeState value137) 4064#usize
 def indices08 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,52#u32,60#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value128,encodeState value129]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 60#u32 8#usize (encodeState value138) 4096#usize
 def indices09 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32,60#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value129]
def output (s : reference.Scratch) : reference.Scratch := {s09 s with n:=9#usize}
 def indicesOut : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      3840#usize 3872#usize)=ok (encodeState (JGc_TX2_HashBytes.state [254,14,130,135,247,205,115,79,107,166,89,198,117,201,141,89,5,159,55,163,8,155,248,77,113,14,97,138,39,216,58,208])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3840#usize 3872#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3840#usize 3872#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [254,14,130,135,247,205,115,79,107,166,89,198,117,201,141,89,5,159,55,163,8,155,248,77,113,14,97,138,39,216,58,208])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3840).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 32199).take 32)=(encodeState (JGc_TX2_HashBytes.state [254,14,130,135,247,205,115,79,107,166,89,198,117,201,141,89,5,159,55,163,8,155,248,77,113,14,97,138,39,216,58,208])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3840#usize 3872#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [254,14,130,135,247,205,115,79,107,166,89,198,117,201,141,89,5,159,55,163,8,155,248,77,113,14,97,138,39,216,58,208])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [254,14,130,135,247,205,115,79,107,166,89,198,117,201,141,89,5,159,55,163,8,155,248,77,113,14,97,138,39,216,58,208]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [254,14,130,135,247,205,115,79,107,166,89,198,117,201,141,89,5,159,55,163,8,155,248,77,113,14,97,138,39,216,58,208])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      3872#usize 3904#usize)=ok (encodeState (JGc_TX2_HashBytes.state [66,225,29,27,146,87,4,138,36,32,56,196,112,123,143,15,189,101,254,171,108,124,109,6,10,176,21,23,227,251,248,124])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3872#usize 3904#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3872#usize 3904#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [66,225,29,27,146,87,4,138,36,32,56,196,112,123,143,15,189,101,254,171,108,124,109,6,10,176,21,23,227,251,248,124])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3872).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 32231).take 32)=(encodeState (JGc_TX2_HashBytes.state [66,225,29,27,146,87,4,138,36,32,56,196,112,123,143,15,189,101,254,171,108,124,109,6,10,176,21,23,227,251,248,124])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3872#usize 3904#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [66,225,29,27,146,87,4,138,36,32,56,196,112,123,143,15,189,101,254,171,108,124,109,6,10,176,21,23,227,251,248,124])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [66,225,29,27,146,87,4,138,36,32,56,196,112,123,143,15,189,101,254,171,108,124,109,6,10,176,21,23,227,251,248,124]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [66,225,29,27,146,87,4,138,36,32,56,196,112,123,143,15,189,101,254,171,108,124,109,6,10,176,21,23,227,251,248,124])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      3904#usize 3936#usize)=ok (encodeState (JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3904#usize 3936#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3904#usize 3936#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3904).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 32263).take 32)=(encodeState (JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3904#usize 3936#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      3936#usize 3968#usize)=ok (encodeState (JGc_TX2_HashBytes.state [188,195,79,74,213,254,47,21,205,195,209,166,40,141,13,9,97,84,152,93,102,191,158,16,165,158,96,183,21,248,100,55])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3936#usize 3968#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3936#usize 3968#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [188,195,79,74,213,254,47,21,205,195,209,166,40,141,13,9,97,84,152,93,102,191,158,16,165,158,96,183,21,248,100,55])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3936).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 32295).take 32)=(encodeState (JGc_TX2_HashBytes.state [188,195,79,74,213,254,47,21,205,195,209,166,40,141,13,9,97,84,152,93,102,191,158,16,165,158,96,183,21,248,100,55])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3936#usize 3968#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [188,195,79,74,213,254,47,21,205,195,209,166,40,141,13,9,97,84,152,93,102,191,158,16,165,158,96,183,21,248,100,55])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [188,195,79,74,213,254,47,21,205,195,209,166,40,141,13,9,97,84,152,93,102,191,158,16,165,158,96,183,21,248,100,55]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [188,195,79,74,213,254,47,21,205,195,209,166,40,141,13,9,97,84,152,93,102,191,158,16,165,158,96,183,21,248,100,55])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      3968#usize 4000#usize)=ok (encodeState (JGc_TX2_HashBytes.state [187,76,51,74,59,158,50,38,87,85,221,77,230,156,105,93,240,119,203,74,247,195,29,178,103,62,94,105,26,121,227,113])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3968#usize 4000#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3968#usize 4000#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [187,76,51,74,59,158,50,38,87,85,221,77,230,156,105,93,240,119,203,74,247,195,29,178,103,62,94,105,26,121,227,113])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3968).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 32327).take 32)=(encodeState (JGc_TX2_HashBytes.state [187,76,51,74,59,158,50,38,87,85,221,77,230,156,105,93,240,119,203,74,247,195,29,178,103,62,94,105,26,121,227,113])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3968#usize 4000#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [187,76,51,74,59,158,50,38,87,85,221,77,230,156,105,93,240,119,203,74,247,195,29,178,103,62,94,105,26,121,227,113])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [187,76,51,74,59,158,50,38,87,85,221,77,230,156,105,93,240,119,203,74,247,195,29,178,103,62,94,105,26,121,227,113]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [187,76,51,74,59,158,50,38,87,85,221,77,230,156,105,93,240,119,203,74,247,195,29,178,103,62,94,105,26,121,227,113])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      4000#usize 4032#usize)=ok (encodeState (JGc_TX2_HashBytes.state [73,20,30,234,180,192,147,217,52,97,111,104,183,231,180,130,207,5,13,223,218,43,82,64,97,51,35,212,32,222,55,133])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 4000#usize 4032#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 4000#usize 4032#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [73,20,30,234,180,192,147,217,52,97,111,104,183,231,180,130,207,5,13,223,218,43,82,64,97,51,35,212,32,222,55,133])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 4000).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 32359).take 32)=(encodeState (JGc_TX2_HashBytes.state [73,20,30,234,180,192,147,217,52,97,111,104,183,231,180,130,207,5,13,223,218,43,82,64,97,51,35,212,32,222,55,133])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 4000#usize 4032#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [73,20,30,234,180,192,147,217,52,97,111,104,183,231,180,130,207,5,13,223,218,43,82,64,97,51,35,212,32,222,55,133])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [73,20,30,234,180,192,147,217,52,97,111,104,183,231,180,130,207,5,13,223,218,43,82,64,97,51,35,212,32,222,55,133]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [73,20,30,234,180,192,147,217,52,97,111,104,183,231,180,130,207,5,13,223,218,43,82,64,97,51,35,212,32,222,55,133])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      4032#usize 4064#usize)=ok (encodeState (JGc_TX2_HashBytes.state [216,39,125,52,179,150,49,41,23,46,71,20,106,158,77,0,176,105,197,0,58,234,126,198,61,27,243,66,155,192,133,151])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 4032#usize 4064#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 4032#usize 4064#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [216,39,125,52,179,150,49,41,23,46,71,20,106,158,77,0,176,105,197,0,58,234,126,198,61,27,243,66,155,192,133,151])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 4032).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 32391).take 32)=(encodeState (JGc_TX2_HashBytes.state [216,39,125,52,179,150,49,41,23,46,71,20,106,158,77,0,176,105,197,0,58,234,126,198,61,27,243,66,155,192,133,151])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 4032#usize 4064#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [216,39,125,52,179,150,49,41,23,46,71,20,106,158,77,0,176,105,197,0,58,234,126,198,61,27,243,66,155,192,133,151])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [216,39,125,52,179,150,49,41,23,46,71,20,106,158,77,0,176,105,197,0,58,234,126,198,61,27,243,66,155,192,133,151]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [216,39,125,52,179,150,49,41,23,46,71,20,106,158,77,0,176,105,197,0,58,234,126,198,61,27,243,66,155,192,133,151])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      4064#usize 4096#usize)=ok (encodeState (JGc_TX2_HashBytes.state [24,83,241,162,249,154,230,253,165,145,84,5,188,201,216,39,216,112,35,240,228,235,23,16,186,131,61,83,162,137,67,145])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 4064#usize 4096#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 4064#usize 4096#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [24,83,241,162,249,154,230,253,165,145,84,5,188,201,216,39,216,112,35,240,228,235,23,16,186,131,61,83,162,137,67,145])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 4064).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 32423).take 32)=(encodeState (JGc_TX2_HashBytes.state [24,83,241,162,249,154,230,253,165,145,84,5,188,201,216,39,216,112,35,240,228,235,23,16,186,131,61,83,162,137,67,145])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 4064#usize 4096#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [24,83,241,162,249,154,230,253,165,145,84,5,188,201,216,39,216,112,35,240,228,235,23,16,186,131,61,83,162,137,67,145])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [24,83,241,162,249,154,230,253,165,145,84,5,188,201,216,39,216,112,35,240,228,235,23,16,186,131,61,83,162,137,67,145]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [24,83,241,162,249,154,230,253,165,145,84,5,188,201,216,39,216,112,35,240,228,235,23,16,186,131,61,83,162,137,67,145])).property];decide)
  exact same ▸ run
#print axioms read08
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3840) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGu_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
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
  have read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s00 s).«at» 3872#usize)=ok (encodeState (JGc_TX2_HashBytes.state [254,14,130,135,247,205,115,79,107,166,89,198,117,201,141,89,5,159,55,163,8,155,248,77,113,14,97,138,39,216,58,208])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGu_Supplied.nodes0 0#usize 0#usize 1#usize 3872#usize 576#usize
    16#u32 (encodeState value120) (encodeState (JGc_TX2_HashBytes.state [254,14,130,135,247,205,115,79,107,166,89,198,117,201,141,89,5,159,55,163,8,155,248,77,113,14,97,138,39,216,58,208])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGu_Supplied.length0];decide) read00
  simp only [show 16#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGu_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGu_ParentCalls0.source130 D hash (s00 s) 1#usize 3872#usize 16#u32 0#usize (by decide)
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
  have read01 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s01 s).«at» 3904#usize)=ok (encodeState (JGc_TX2_HashBytes.state [66,225,29,27,146,87,4,138,36,32,56,196,112,123,143,15,189,101,254,171,108,124,109,6,10,176,21,23,227,251,248,124])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGu_Supplied.nodes0 1#usize 1#usize 2#usize 3904#usize 544#usize
    22#u32 (encodeState value121) (encodeState (JGc_TX2_HashBytes.state [66,225,29,27,146,87,4,138,36,32,56,196,112,123,143,15,189,101,254,171,108,124,109,6,10,176,21,23,227,251,248,124])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGu_Supplied.length0];decide) read01
  simp only [show 22#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGu_Supplied.nodes0 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGu_ParentCalls0.source131 D hash (s01 s) 2#usize 3904#usize 22#u32 1#usize (by decide)
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
  have read02 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s02 s).«at» 3936#usize)=ok (encodeState (JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGu_Supplied.nodes0 2#usize 2#usize 3#usize 3936#usize 512#usize
    36#u32 (encodeState value122) (encodeState (JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGu_Supplied.length0];decide) read02
  simp only [show 36#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGu_Supplied.nodes0 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGu_ParentCalls0.source132 D hash (s02 s) 3#usize 3936#usize 36#u32 2#usize (by decide)
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
  have read03 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s03 s).«at» 3968#usize)=ok (encodeState (JGc_TX2_HashBytes.state [188,195,79,74,213,254,47,21,205,195,209,166,40,141,13,9,97,84,152,93,102,191,158,16,165,158,96,183,21,248,100,55])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGu_Supplied.nodes0 3#usize 3#usize 4#usize 3968#usize 480#usize
    39#u32 (encodeState value123) (encodeState (JGc_TX2_HashBytes.state [188,195,79,74,213,254,47,21,205,195,209,166,40,141,13,9,97,84,152,93,102,191,158,16,165,158,96,183,21,248,100,55])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGu_Supplied.length0];decide) read03
  simp only [show 39#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGu_Supplied.nodes0 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGu_ParentCalls0.source133 D hash (s03 s) 4#usize 3968#usize 39#u32 3#usize (by decide)
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
  have read04 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s04 s).«at» 4000#usize)=ok (encodeState (JGc_TX2_HashBytes.state [187,76,51,74,59,158,50,38,87,85,221,77,230,156,105,93,240,119,203,74,247,195,29,178,103,62,94,105,26,121,227,113])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGu_Supplied.nodes0 4#usize 4#usize 5#usize 4000#usize 448#usize
    44#u32 (encodeState value124) (encodeState (JGc_TX2_HashBytes.state [187,76,51,74,59,158,50,38,87,85,221,77,230,156,105,93,240,119,203,74,247,195,29,178,103,62,94,105,26,121,227,113])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGu_Supplied.length0];decide) read04
  simp only [show 44#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGu_Supplied.nodes0 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGu_ParentCalls0.source134 D hash (s04 s) 5#usize 4000#usize 44#u32 4#usize (by decide)
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
  have selected05 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGu_Supplied.nodes0 5#usize 5#usize 6#usize 7#usize 46#u32
    (encodeState value125) (encodeState value126) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (6:Nat)<(s05 s).n.val;rw [v05.size];decide)
    rn05 rr05 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGu_Supplied.nodes0 5#usize 5#usize=
        ok (.Next (s06 s) 7#usize 6#usize) := by
    rw [selected05]
    rw [cursor05]
    exact JGu_ParentCalls0.source135 D hash (s05 s) 7#usize 4000#usize 46#u32 5#usize (by decide)
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
  have read06 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s06 s).«at» 4032#usize)=ok (encodeState (JGc_TX2_HashBytes.state [73,20,30,234,180,192,147,217,52,97,111,104,183,231,180,130,207,5,13,223,218,43,82,64,97,51,35,212,32,222,55,133])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGu_Supplied.nodes0 7#usize 6#usize 8#usize 4032#usize 416#usize
    51#u32 (encodeState value127) (encodeState (JGc_TX2_HashBytes.state [73,20,30,234,180,192,147,217,52,97,111,104,183,231,180,130,207,5,13,223,218,43,82,64,97,51,35,212,32,222,55,133])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGu_Supplied.length0];decide) read06
  simp only [show 51#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGu_Supplied.nodes0 7#usize 6#usize=
        ok (.Next (s07 s) 8#usize 7#usize) := by
    rw [selected06]
    exact JGu_ParentCalls0.source136 D hash (s06 s) 8#usize 4032#usize 51#u32 6#usize (by decide)
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
  have read07 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s07 s).«at» 4064#usize)=ok (encodeState (JGc_TX2_HashBytes.state [216,39,125,52,179,150,49,41,23,46,71,20,106,158,77,0,176,105,197,0,58,234,126,198,61,27,243,66,155,192,133,151])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGu_Supplied.nodes0 8#usize 7#usize 9#usize 4064#usize 384#usize
    52#u32 (encodeState value128) (encodeState (JGc_TX2_HashBytes.state [216,39,125,52,179,150,49,41,23,46,71,20,106,158,77,0,176,105,197,0,58,234,126,198,61,27,243,66,155,192,133,151])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGu_Supplied.length0];decide) read07
  simp only [show 52#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGu_Supplied.nodes0 8#usize 7#usize=
        ok (.Next (s08 s) 9#usize 8#usize) := by
    rw [selected07]
    exact JGu_ParentCalls0.source137 D hash (s07 s) 9#usize 4064#usize 52#u32 7#usize (by decide)
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
  have read08 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s08 s).«at» 4096#usize)=ok (encodeState (JGc_TX2_HashBytes.state [24,83,241,162,249,154,230,253,165,145,84,5,188,201,216,39,216,112,35,240,228,235,23,16,186,131,61,83,162,137,67,145])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGu_Supplied.nodes0 9#usize 8#usize 10#usize 4096#usize 352#usize
    60#u32 (encodeState value129) (encodeState (JGc_TX2_HashBytes.state [24,83,241,162,249,154,230,253,165,145,84,5,188,201,216,39,216,112,35,240,228,235,23,16,186,131,61,83,162,137,67,145])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGu_Supplied.length0];decide) read08
  simp only [show 60#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGu_Supplied.nodes0 9#usize 8#usize=
        ok (.Next (s09 s) 10#usize 9#usize) := by
    rw [selected08]
    exact JGu_ParentCalls0.source138 D hash (s08 s) 10#usize 4096#usize 60#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 4096 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 4064 v08
      60#u32 8#usize (encodeState value138) 4096#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGu_Supplied.nodes0 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGu_Supplied.nodes0 1#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGu_Supplied.nodes0 2#usize 2#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGu_Supplied.nodes0 3#usize 3#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGu_Supplied.nodes0 4#usize 4#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGu_Supplied.nodes0 5#usize 5#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGu_Supplied.nodes0 7#usize 6#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGu_Supplied.nodes0 8#usize 7#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGu_Supplied.nodes0 9#usize 8#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGu_Supplied.nodes0 10#usize 9#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s09 s).n.val≤10;rw [v09.size];decide)
  · exact JGm_TX2_View.finish (s09 s) indices09 values09 4096
      v09 9#usize (by decide)
#print axioms source
end AspisR1.JGu_Level0_12
end
