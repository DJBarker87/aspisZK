import JGu_ParentCalls2
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
namespace AspisR1.JGu_Level2_11
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGu_Supplied.nodes2
def indices00 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
def values00 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 8#u32 0#usize (encodeState value119) 3488#usize
 def indices01 : List U32 := [4#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value119,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 11#u32 1#usize (encodeState value120) 3520#usize
 def indices02 : List U32 := [4#u32,5#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value119,encodeState value120,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 18#u32 2#usize (encodeState value121) 3520#usize
 def indices03 : List U32 := [4#u32,5#u32,9#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value119,encodeState value120,encodeState value121,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 22#u32 3#usize (encodeState value122) 3520#usize
 def indices04 : List U32 := [4#u32,5#u32,9#u32,11#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value119,encodeState value120,encodeState value121,encodeState value122,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 25#u32 4#usize (encodeState value123) 3552#usize
 def indices05 : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,23#u32,25#u32,26#u32,30#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value119,encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value115,encodeState value116,encodeState value117,encodeState value118]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 26#u32 5#usize (encodeState value124) 3584#usize
 def indices06 : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,13#u32,25#u32,26#u32,30#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value119,encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value116,encodeState value117,encodeState value118]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 30#u32 6#usize (encodeState value125) 3616#usize
 def indices07 : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,13#u32,15#u32,26#u32,30#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value119,encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value117,encodeState value118]
def output (s : reference.Scratch) : reference.Scratch := {s07 s with n:=7#usize}
 def indicesOut : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,13#u32,15#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value119,encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      3456#usize 3488#usize)=ok (encodeState (JGc_TX2_HashBytes.state [170,153,117,5,67,73,116,195,9,13,223,78,171,169,18,95,110,140,91,37,34,17,55,253,160,219,151,107,246,215,123,234])) := by
  unfold JGu_Supplied.nodes2
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3456#usize 3488#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3456#usize 3488#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [170,153,117,5,67,73,116,195,9,13,223,78,171,169,18,95,110,140,91,37,34,17,55,253,160,219,151,107,246,215,123,234])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3456).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41159).take 32)=(encodeState (JGc_TX2_HashBytes.state [170,153,117,5,67,73,116,195,9,13,223,78,171,169,18,95,110,140,91,37,34,17,55,253,160,219,151,107,246,215,123,234])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3456#usize 3488#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [170,153,117,5,67,73,116,195,9,13,223,78,171,169,18,95,110,140,91,37,34,17,55,253,160,219,151,107,246,215,123,234])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [170,153,117,5,67,73,116,195,9,13,223,78,171,169,18,95,110,140,91,37,34,17,55,253,160,219,151,107,246,215,123,234]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [170,153,117,5,67,73,116,195,9,13,223,78,171,169,18,95,110,140,91,37,34,17,55,253,160,219,151,107,246,215,123,234])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      3488#usize 3520#usize)=ok (encodeState (JGc_TX2_HashBytes.state [216,219,166,205,15,70,186,97,80,104,229,181,34,249,182,130,33,182,45,106,240,203,133,32,164,178,203,167,172,135,153,82])) := by
  unfold JGu_Supplied.nodes2
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3488#usize 3520#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3488#usize 3520#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [216,219,166,205,15,70,186,97,80,104,229,181,34,249,182,130,33,182,45,106,240,203,133,32,164,178,203,167,172,135,153,82])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3488).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41191).take 32)=(encodeState (JGc_TX2_HashBytes.state [216,219,166,205,15,70,186,97,80,104,229,181,34,249,182,130,33,182,45,106,240,203,133,32,164,178,203,167,172,135,153,82])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3488#usize 3520#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [216,219,166,205,15,70,186,97,80,104,229,181,34,249,182,130,33,182,45,106,240,203,133,32,164,178,203,167,172,135,153,82])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [216,219,166,205,15,70,186,97,80,104,229,181,34,249,182,130,33,182,45,106,240,203,133,32,164,178,203,167,172,135,153,82]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [216,219,166,205,15,70,186,97,80,104,229,181,34,249,182,130,33,182,45,106,240,203,133,32,164,178,203,167,172,135,153,82])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      3520#usize 3552#usize)=ok (encodeState (JGc_TX2_HashBytes.state [60,65,38,140,93,216,131,203,27,50,149,248,16,182,251,250,174,83,223,189,145,180,153,159,227,187,210,101,127,209,224,34])) := by
  unfold JGu_Supplied.nodes2
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3520#usize 3552#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3520#usize 3552#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [60,65,38,140,93,216,131,203,27,50,149,248,16,182,251,250,174,83,223,189,145,180,153,159,227,187,210,101,127,209,224,34])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3520).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41223).take 32)=(encodeState (JGc_TX2_HashBytes.state [60,65,38,140,93,216,131,203,27,50,149,248,16,182,251,250,174,83,223,189,145,180,153,159,227,187,210,101,127,209,224,34])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3520#usize 3552#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [60,65,38,140,93,216,131,203,27,50,149,248,16,182,251,250,174,83,223,189,145,180,153,159,227,187,210,101,127,209,224,34])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [60,65,38,140,93,216,131,203,27,50,149,248,16,182,251,250,174,83,223,189,145,180,153,159,227,187,210,101,127,209,224,34]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [60,65,38,140,93,216,131,203,27,50,149,248,16,182,251,250,174,83,223,189,145,180,153,159,227,187,210,101,127,209,224,34])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      3552#usize 3584#usize)=ok (encodeState (JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216])) := by
  unfold JGu_Supplied.nodes2
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3552#usize 3584#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3552#usize 3584#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3552).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41255).take 32)=(encodeState (JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3552#usize 3584#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      3584#usize 3616#usize)=ok (encodeState (JGc_TX2_HashBytes.state [197,225,37,96,40,16,98,217,159,88,149,106,254,188,227,153,131,207,22,77,128,46,74,234,41,2,48,235,27,112,230,153])) := by
  unfold JGu_Supplied.nodes2
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3584#usize 3616#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3584#usize 3616#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [197,225,37,96,40,16,98,217,159,88,149,106,254,188,227,153,131,207,22,77,128,46,74,234,41,2,48,235,27,112,230,153])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3584).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41287).take 32)=(encodeState (JGc_TX2_HashBytes.state [197,225,37,96,40,16,98,217,159,88,149,106,254,188,227,153,131,207,22,77,128,46,74,234,41,2,48,235,27,112,230,153])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3584#usize 3616#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [197,225,37,96,40,16,98,217,159,88,149,106,254,188,227,153,131,207,22,77,128,46,74,234,41,2,48,235,27,112,230,153])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [197,225,37,96,40,16,98,217,159,88,149,106,254,188,227,153,131,207,22,77,128,46,74,234,41,2,48,235,27,112,230,153]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [197,225,37,96,40,16,98,217,159,88,149,106,254,188,227,153,131,207,22,77,128,46,74,234,41,2,48,235,27,112,230,153])).property];decide)
  exact same ▸ run
#print axioms read06
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3456) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3616 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3456 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 8#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3456 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value110) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3456 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3456#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠8#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨11#u32,JGm_TX2_View.index (s00 s) indices00 values00 3456 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      (s00 s).«at» 3488#usize)=ok (encodeState (JGc_TX2_HashBytes.state [170,153,117,5,67,73,116,195,9,13,223,78,171,169,18,95,110,140,91,37,34,17,55,253,160,219,151,107,246,215,123,234])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGu_Supplied.nodes2 0#usize 0#usize 1#usize 3488#usize 384#usize
    8#u32 (encodeState value110) (encodeState (JGc_TX2_HashBytes.state [170,153,117,5,67,73,116,195,9,13,223,78,171,169,18,95,110,140,91,37,34,17,55,253,160,219,151,107,246,215,123,234])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGu_Supplied.length2];decide) read00
  simp only [show 8#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGu_ParentCalls2.source119 D hash (s00 s) 1#usize 3488#usize 8#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3488 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3456 v00
      8#u32 0#usize (encodeState value119) 3488#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 11#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 3488 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value111) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3488 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=3488#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠11#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨18#u32,JGm_TX2_View.index (s01 s) indices01 values01 3488 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      (s01 s).«at» 3520#usize)=ok (encodeState (JGc_TX2_HashBytes.state [216,219,166,205,15,70,186,97,80,104,229,181,34,249,182,130,33,182,45,106,240,203,133,32,164,178,203,167,172,135,153,82])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGu_Supplied.nodes2 1#usize 1#usize 2#usize 3520#usize 352#usize
    11#u32 (encodeState value111) (encodeState (JGc_TX2_HashBytes.state [216,219,166,205,15,70,186,97,80,104,229,181,34,249,182,130,33,182,45,106,240,203,133,32,164,178,203,167,172,135,153,82])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGu_Supplied.length2];decide) read01
  simp only [show 11#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGu_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGu_ParentCalls2.source120 D hash (s01 s) 2#usize 3520#usize 11#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 3520 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 3488 v01
      11#u32 1#usize (encodeState value120) 3520#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 18#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 3520 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value112) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3520 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=3520#usize := UScalar.eq_of_val_eq v02.at_eq
  have rn02 : Array.index_usize (s02 s).idx 3#usize=ok (18#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s02 s) indices02 values02 3520 v02 3#usize (by decide)
  have rr02 : Array.index_usize (s02 s).val 3#usize=ok (encodeState value113) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3520 v02 3#usize (by decide)
  have selected02 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGu_Supplied.nodes2 2#usize 2#usize 3#usize 4#usize 18#u32
    (encodeState value112) (encodeState value113) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (3:Nat)<(s02 s).n.val;rw [v02.size];decide)
    rn02 rr02 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGu_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 4#usize 3#usize) := by
    rw [selected02]
    rw [cursor02]
    exact JGu_ParentCalls2.source121 D hash (s02 s) 4#usize 3520#usize 18#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 3520 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 3520 v02
      18#u32 2#usize (encodeState value121) 3520#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 4#usize=ok 22#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 3520 v03 4#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 4#usize=ok (encodeState value114) :=
    JGm_TX2_View.value (s03 s) indices03 values03 3520 v03 4#usize (by decide)
  have active03 : 4#usize<(s03 s).n := by
    change (4:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=3520#usize := UScalar.eq_of_val_eq v03.at_eq
  have rn03 : Array.index_usize (s03 s).idx 5#usize=ok (22#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s03 s) indices03 values03 3520 v03 5#usize (by decide)
  have rr03 : Array.index_usize (s03 s).val 5#usize=ok (encodeState value115) :=
    JGm_TX2_View.value (s03 s) indices03 values03 3520 v03 5#usize (by decide)
  have selected03 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGu_Supplied.nodes2 4#usize 3#usize 5#usize 6#usize 22#u32
    (encodeState value114) (encodeState value115) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (5:Nat)<(s03 s).n.val;rw [v03.size];decide)
    rn03 rr03 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGu_Supplied.nodes2 4#usize 3#usize=
        ok (.Next (s04 s) 6#usize 4#usize) := by
    rw [selected03]
    rw [cursor03]
    exact JGu_ParentCalls2.source122 D hash (s03 s) 6#usize 3520#usize 22#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 3520 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 3520 v03
      22#u32 3#usize (encodeState value122) 3520#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 6#usize=ok 25#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 3520 v04 6#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 6#usize=ok (encodeState value116) :=
    JGm_TX2_View.value (s04 s) indices04 values04 3520 v04 6#usize (by decide)
  have active04 : 6#usize<(s04 s).n := by
    change (6:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=3520#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 7#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 7#usize=ok other ∧ other≠25#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨26#u32,JGm_TX2_View.index (s04 s) indices04 values04 3520 v04 7#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      (s04 s).«at» 3552#usize)=ok (encodeState (JGc_TX2_HashBytes.state [60,65,38,140,93,216,131,203,27,50,149,248,16,182,251,250,174,83,223,189,145,180,153,159,227,187,210,101,127,209,224,34])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGu_Supplied.nodes2 6#usize 4#usize 7#usize 3552#usize 320#usize
    25#u32 (encodeState value116) (encodeState (JGc_TX2_HashBytes.state [60,65,38,140,93,216,131,203,27,50,149,248,16,182,251,250,174,83,223,189,145,180,153,159,227,187,210,101,127,209,224,34])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGu_Supplied.length2];decide) read04
  simp only [show 25#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGu_Supplied.nodes2 6#usize 4#usize=
        ok (.Next (s05 s) 7#usize 5#usize) := by
    rw [selected04]
    exact JGu_ParentCalls2.source123 D hash (s04 s) 7#usize 3552#usize 25#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 3552 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 3520 v04
      25#u32 4#usize (encodeState value123) 3552#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 7#usize=ok 26#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 3552 v05 7#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 7#usize=ok (encodeState value117) :=
    JGm_TX2_View.value (s05 s) indices05 values05 3552 v05 7#usize (by decide)
  have active05 : 7#usize<(s05 s).n := by
    change (7:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=3552#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 8#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 8#usize=ok other ∧ other≠26#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨30#u32,JGm_TX2_View.index (s05 s) indices05 values05 3552 v05 8#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      (s05 s).«at» 3584#usize)=ok (encodeState (JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGu_Supplied.nodes2 7#usize 5#usize 8#usize 3584#usize 288#usize
    26#u32 (encodeState value117) (encodeState (JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGu_Supplied.length2];decide) read05
  simp only [show 26#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGu_Supplied.nodes2 7#usize 5#usize=
        ok (.Next (s06 s) 8#usize 6#usize) := by
    rw [selected05]
    exact JGu_ParentCalls2.source124 D hash (s05 s) 8#usize 3584#usize 26#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 3584 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 3552 v05
      26#u32 5#usize (encodeState value124) 3584#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 8#usize=ok 30#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 3584 v06 8#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 8#usize=ok (encodeState value118) :=
    JGm_TX2_View.value (s06 s) indices06 values06 3584 v06 8#usize (by decide)
  have active06 : 8#usize<(s06 s).n := by
    change (8:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=3584#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 9#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 9#usize=ok other ∧ other≠30#u32 ^^^ 1#u32 := by
    intro more
    change (9:Nat)<(s06 s).n.val at more
    rw [v06.size] at more
    exact False.elim ((by decide : ¬(9:Nat)<9) more)
  have read06 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      (s06 s).«at» 3616#usize)=ok (encodeState (JGc_TX2_HashBytes.state [197,225,37,96,40,16,98,217,159,88,149,106,254,188,227,153,131,207,22,77,128,46,74,234,41,2,48,235,27,112,230,153])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGu_Supplied.nodes2 8#usize 6#usize 9#usize 3616#usize 256#usize
    30#u32 (encodeState value118) (encodeState (JGc_TX2_HashBytes.state [197,225,37,96,40,16,98,217,159,88,149,106,254,188,227,153,131,207,22,77,128,46,74,234,41,2,48,235,27,112,230,153])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGu_Supplied.length2];decide) read06
  simp only [show 30#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGu_Supplied.nodes2 8#usize 6#usize=
        ok (.Next (s07 s) 9#usize 7#usize) := by
    rw [selected06]
    exact JGu_ParentCalls2.source125 D hash (s06 s) 9#usize 3616#usize 30#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 3616 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 3584 v06
      30#u32 6#usize (encodeState value125) 3616#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGu_Supplied.nodes2 1#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGu_Supplied.nodes2 2#usize 2#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGu_Supplied.nodes2 4#usize 3#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGu_Supplied.nodes2 6#usize 4#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGu_Supplied.nodes2 7#usize 5#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGu_Supplied.nodes2 8#usize 6#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGu_Supplied.nodes2 9#usize 7#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s07 s).n.val≤9;rw [v07.size];decide)
  · exact JGm_TX2_View.finish (s07 s) indices07 values07 3616
      v07 7#usize (by decide)
#print axioms source
end AspisR1.JGu_Level2_11
end
