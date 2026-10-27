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
namespace AspisR1.JGu_Level1_14
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGu_Supplied.nodes1
def indices00 : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,13#u32,15#u32]
def values00 : List (Array U8 32#usize) := [encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143,encodeState value144,encodeState value145]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 4#u32 0#usize (encodeState value146) 4256#usize
 def indices01 : List U32 := [2#u32,5#u32,9#u32,11#u32,12#u32,13#u32,15#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value146,encodeState value140,encodeState value141,encodeState value142,encodeState value143,encodeState value144,encodeState value145]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 9#u32 1#usize (encodeState value147) 4288#usize
 def indices02 : List U32 := [2#u32,4#u32,9#u32,11#u32,12#u32,13#u32,15#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value146,encodeState value147,encodeState value141,encodeState value142,encodeState value143,encodeState value144,encodeState value145]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 11#u32 2#usize (encodeState value148) 4320#usize
 def indices03 : List U32 := [2#u32,4#u32,5#u32,11#u32,12#u32,13#u32,15#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value146,encodeState value147,encodeState value148,encodeState value142,encodeState value143,encodeState value144,encodeState value145]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 12#u32 3#usize (encodeState value149) 4320#usize
 def indices04 : List U32 := [2#u32,4#u32,5#u32,6#u32,12#u32,13#u32,15#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value143,encodeState value144,encodeState value145]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 15#u32 4#usize (encodeState value150) 4352#usize
 def indices05 : List U32 := [2#u32,4#u32,5#u32,6#u32,7#u32,13#u32,15#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150,encodeState value144,encodeState value145]
def output (s : reference.Scratch) : reference.Scratch := {s05 s with n:=5#usize}
 def indicesOut : List U32 := [2#u32,4#u32,5#u32,6#u32,7#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150]
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      4256#usize 4288#usize)=ok (encodeState (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225])) := by
  unfold JGu_Supplied.nodes1
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4256#usize 4288#usize (by decide) (by decide)]
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
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      4288#usize 4320#usize)=ok (encodeState (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139])) := by
  unfold JGu_Supplied.nodes1
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4288#usize 4320#usize (by decide) (by decide)]
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
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      4320#usize 4352#usize)=ok (encodeState (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193])) := by
  unfold JGu_Supplied.nodes1
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4320#usize 4352#usize (by decide) (by decide)]
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
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
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
  have selected00 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGu_Supplied.nodes1 0#usize 0#usize 1#usize 2#usize 4#u32
    (encodeState value139) (encodeState value140) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (1:Nat)<(s00 s).n.val;rw [v00.size];decide)
    rn00 rr00 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 2#usize 1#usize) := by
    rw [selected00]
    rw [cursor00]
    exact JGu_ParentCalls1.source146 D hash (s00 s) 2#usize 4256#usize 4#u32 0#usize (by decide)
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
  have read01 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      (s01 s).«at» 4288#usize)=ok (encodeState (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGu_Supplied.nodes1 2#usize 1#usize 3#usize 4288#usize 160#usize
    9#u32 (encodeState value141) (encodeState (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length1
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGu_Supplied.length1];decide) read01
  simp only [show 9#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGu_Supplied.nodes1 2#usize 1#usize=
        ok (.Next (s02 s) 3#usize 2#usize) := by
    rw [selected01]
    exact JGu_ParentCalls1.source147 D hash (s01 s) 3#usize 4288#usize 9#u32 1#usize (by decide)
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
  have read02 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      (s02 s).«at» 4320#usize)=ok (encodeState (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGu_Supplied.nodes1 3#usize 2#usize 4#usize 4320#usize 128#usize
    11#u32 (encodeState value142) (encodeState (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length1
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGu_Supplied.length1];decide) read02
  simp only [show 11#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGu_Supplied.nodes1 3#usize 2#usize=
        ok (.Next (s03 s) 4#usize 3#usize) := by
    rw [selected02]
    exact JGu_ParentCalls1.source148 D hash (s02 s) 4#usize 4320#usize 11#u32 2#usize (by decide)
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
  have selected03 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGu_Supplied.nodes1 4#usize 3#usize 5#usize 6#usize 12#u32
    (encodeState value143) (encodeState value144) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (5:Nat)<(s03 s).n.val;rw [v03.size];decide)
    rn03 rr03 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGu_Supplied.nodes1 4#usize 3#usize=
        ok (.Next (s04 s) 6#usize 4#usize) := by
    rw [selected03]
    rw [cursor03]
    exact JGu_ParentCalls1.source149 D hash (s03 s) 6#usize 4320#usize 12#u32 3#usize (by decide)
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
  have read04 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      (s04 s).«at» 4352#usize)=ok (encodeState (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGu_Supplied.nodes1 6#usize 4#usize 7#usize 4352#usize 96#usize
    15#u32 (encodeState value145) (encodeState (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length1
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGu_Supplied.length1];decide) read04
  simp only [show 15#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGu_Supplied.nodes1 6#usize 4#usize=
        ok (.Next (s05 s) 7#usize 5#usize) := by
    rw [selected04]
    exact JGu_ParentCalls1.source150 D hash (s04 s) 7#usize 4352#usize 15#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 4352 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 4320 v04
      15#u32 4#usize (encodeState value150) 4352#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGu_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGu_Supplied.nodes1 2#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGu_Supplied.nodes1 3#usize 2#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGu_Supplied.nodes1 4#usize 3#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGu_Supplied.nodes1 6#usize 4#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGu_Supplied.nodes1 7#usize 5#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s05 s).n.val≤7;rw [v05.size];decide)
  · exact JGm_TX2_View.finish (s05 s) indices05 values05 4352
      v05 5#usize (by decide)
#print axioms source
end AspisR1.JGu_Level1_14
end
