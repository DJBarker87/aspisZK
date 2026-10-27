import JGu_ParentCalls1
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
namespace AspisR1.JGu_Level1_13
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGu_Supplied.nodes1
def indices00 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
def values00 : List (Array U8 32#usize) := [encodeState value130,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 8#u32 0#usize (encodeState value139) 4128#usize
 def indices01 : List U32 := [4#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value139,encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 11#u32 1#usize (encodeState value140) 4160#usize
 def indices02 : List U32 := [4#u32,5#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 18#u32 2#usize (encodeState value141) 4160#usize
 def indices03 : List U32 := [4#u32,5#u32,9#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value141,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 22#u32 3#usize (encodeState value142) 4160#usize
 def indices04 : List U32 := [4#u32,5#u32,9#u32,11#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 25#u32 4#usize (encodeState value143) 4192#usize
 def indices05 : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,23#u32,25#u32,26#u32,30#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143,encodeState value135,encodeState value136,encodeState value137,encodeState value138]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 26#u32 5#usize (encodeState value144) 4224#usize
 def indices06 : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,13#u32,25#u32,26#u32,30#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143,encodeState value144,encodeState value136,encodeState value137,encodeState value138]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 30#u32 6#usize (encodeState value145) 4256#usize
 def indices07 : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,13#u32,15#u32,26#u32,30#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143,encodeState value144,encodeState value145,encodeState value137,encodeState value138]
def output (s : reference.Scratch) : reference.Scratch := {s07 s with n:=7#usize}
 def indicesOut : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,13#u32,15#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143,encodeState value144,encodeState value145]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      4096#usize 4128#usize)=ok (encodeState (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242])) := by
  unfold JGu_Supplied.nodes1
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4096#usize 4128#usize (by decide) (by decide)]
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
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      4128#usize 4160#usize)=ok (encodeState (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225])) := by
  unfold JGu_Supplied.nodes1
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4128#usize 4160#usize (by decide) (by decide)]
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
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      4160#usize 4192#usize)=ok (encodeState (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167])) := by
  unfold JGu_Supplied.nodes1
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4160#usize 4192#usize (by decide) (by decide)]
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
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      4192#usize 4224#usize)=ok (encodeState (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27])) := by
  unfold JGu_Supplied.nodes1
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4192#usize 4224#usize (by decide) (by decide)]
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
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      4224#usize 4256#usize)=ok (encodeState (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2])) := by
  unfold JGu_Supplied.nodes1
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4224#usize 4256#usize (by decide) (by decide)]
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
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
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
  have read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      (s00 s).«at» 4128#usize)=ok (encodeState (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGu_Supplied.nodes1 0#usize 0#usize 1#usize 4128#usize 320#usize
    8#u32 (encodeState value130) (encodeState (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length1
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGu_Supplied.length1];decide) read00
  simp only [show 8#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGu_ParentCalls1.source139 D hash (s00 s) 1#usize 4128#usize 8#u32 0#usize (by decide)
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
  have read01 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      (s01 s).«at» 4160#usize)=ok (encodeState (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGu_Supplied.nodes1 1#usize 1#usize 2#usize 4160#usize 288#usize
    11#u32 (encodeState value131) (encodeState (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length1
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGu_Supplied.length1];decide) read01
  simp only [show 11#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGu_ParentCalls1.source140 D hash (s01 s) 2#usize 4160#usize 11#u32 1#usize (by decide)
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
  have selected02 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGu_Supplied.nodes1 2#usize 2#usize 3#usize 4#usize 18#u32
    (encodeState value132) (encodeState value133) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (3:Nat)<(s02 s).n.val;rw [v02.size];decide)
    rn02 rr02 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 4#usize 3#usize) := by
    rw [selected02]
    rw [cursor02]
    exact JGu_ParentCalls1.source141 D hash (s02 s) 4#usize 4160#usize 18#u32 2#usize (by decide)
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
  have selected03 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGu_Supplied.nodes1 4#usize 3#usize 5#usize 6#usize 22#u32
    (encodeState value134) (encodeState value135) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (5:Nat)<(s03 s).n.val;rw [v03.size];decide)
    rn03 rr03 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGu_Supplied.nodes1 4#usize 3#usize=
        ok (.Next (s04 s) 6#usize 4#usize) := by
    rw [selected03]
    rw [cursor03]
    exact JGu_ParentCalls1.source142 D hash (s03 s) 6#usize 4160#usize 22#u32 3#usize (by decide)
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
  have read04 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      (s04 s).«at» 4192#usize)=ok (encodeState (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGu_Supplied.nodes1 6#usize 4#usize 7#usize 4192#usize 256#usize
    25#u32 (encodeState value136) (encodeState (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length1
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGu_Supplied.length1];decide) read04
  simp only [show 25#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGu_Supplied.nodes1 6#usize 4#usize=
        ok (.Next (s05 s) 7#usize 5#usize) := by
    rw [selected04]
    exact JGu_ParentCalls1.source143 D hash (s04 s) 7#usize 4192#usize 25#u32 4#usize (by decide)
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
  have read05 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      (s05 s).«at» 4224#usize)=ok (encodeState (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGu_Supplied.nodes1 7#usize 5#usize 8#usize 4224#usize 224#usize
    26#u32 (encodeState value137) (encodeState (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length1
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGu_Supplied.length1];decide) read05
  simp only [show 26#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGu_Supplied.nodes1 7#usize 5#usize=
        ok (.Next (s06 s) 8#usize 6#usize) := by
    rw [selected05]
    exact JGu_ParentCalls1.source144 D hash (s05 s) 8#usize 4224#usize 26#u32 5#usize (by decide)
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
  have read06 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      (s06 s).«at» 4256#usize)=ok (encodeState (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGu_Supplied.nodes1 8#usize 6#usize 9#usize 4256#usize 192#usize
    30#u32 (encodeState value138) (encodeState (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length1
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGu_Supplied.length1];decide) read06
  simp only [show 30#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGu_Supplied.nodes1 8#usize 6#usize=
        ok (.Next (s07 s) 9#usize 7#usize) := by
    rw [selected06]
    exact JGu_ParentCalls1.source145 D hash (s06 s) 9#usize 4256#usize 30#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 4256 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 4224 v06
      30#u32 6#usize (encodeState value145) 4256#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGu_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGu_Supplied.nodes1 1#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGu_Supplied.nodes1 2#usize 2#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGu_Supplied.nodes1 4#usize 3#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGu_Supplied.nodes1 6#usize 4#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGu_Supplied.nodes1 7#usize 5#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGu_Supplied.nodes1 8#usize 6#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGu_Supplied.nodes1 9#usize 7#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s07 s).n.val≤9;rw [v07.size];decide)
  · exact JGm_TX2_View.finish (s07 s) indices07 values07 4256
      v07 7#usize (by decide)
#print axioms source
end AspisR1.JGu_Level1_13
end
