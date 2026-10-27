import JGy_Tree2Part3
import JGm_TX2_View
import JGy_LightCore
import JGy_LightPadding
import JFw_Frames
import JFq_Range
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JGy_Gu_Level2_12
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGy_Gr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes2
def indices00 : List U32 := [4#u32,5#u32,9#u32,11#u32,12#u32,13#u32,15#u32]
def values00 : List (Array U8 32#usize) := [encodeState value119,encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 4#u32 0#usize (encodeState value126) 3616#usize
 def indices01 : List U32 := [2#u32,5#u32,9#u32,11#u32,12#u32,13#u32,15#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value126,encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 9#u32 1#usize (encodeState value127) 3648#usize
 def indices02 : List U32 := [2#u32,4#u32,9#u32,11#u32,12#u32,13#u32,15#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value126,encodeState value127,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 11#u32 2#usize (encodeState value128) 3680#usize
 def indices03 : List U32 := [2#u32,4#u32,5#u32,11#u32,12#u32,13#u32,15#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value126,encodeState value127,encodeState value128,encodeState value122,encodeState value123,encodeState value124,encodeState value125]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 12#u32 3#usize (encodeState value129) 3680#usize
 def indices04 : List U32 := [2#u32,4#u32,5#u32,6#u32,12#u32,13#u32,15#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value123,encodeState value124,encodeState value125]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 15#u32 4#usize (encodeState value130) 3712#usize
 def indices05 : List U32 := [2#u32,4#u32,5#u32,6#u32,7#u32,13#u32,15#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130,encodeState value124,encodeState value125]
def output (s : reference.Scratch) : reference.Scratch := {s05 s with n:=5#usize}
 def indicesOut : List U32 := [2#u32,4#u32,5#u32,6#u32,7#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130]
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      3616#usize 3648#usize)=ok (encodeState (JGc_TX2_HashBytes.state [224,16,194,66,110,101,52,10,179,79,182,34,88,250,183,144,150,209,247,104,194,136,212,200,251,140,161,235,156,251,89,119])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3616#usize 3648#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3616#usize 3648#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [224,16,194,66,110,101,52,10,179,79,182,34,88,250,183,144,150,209,247,104,194,136,212,200,251,140,161,235,156,251,89,119])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3616).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41319).take 32)=(encodeState (JGc_TX2_HashBytes.state [224,16,194,66,110,101,52,10,179,79,182,34,88,250,183,144,150,209,247,104,194,136,212,200,251,140,161,235,156,251,89,119])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3616#usize 3648#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [224,16,194,66,110,101,52,10,179,79,182,34,88,250,183,144,150,209,247,104,194,136,212,200,251,140,161,235,156,251,89,119])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [224,16,194,66,110,101,52,10,179,79,182,34,88,250,183,144,150,209,247,104,194,136,212,200,251,140,161,235,156,251,89,119]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [224,16,194,66,110,101,52,10,179,79,182,34,88,250,183,144,150,209,247,104,194,136,212,200,251,140,161,235,156,251,89,119])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      3648#usize 3680#usize)=ok (encodeState (JGc_TX2_HashBytes.state [110,140,14,207,117,61,1,50,35,2,166,51,143,145,85,104,230,62,135,43,183,242,18,192,131,122,184,244,45,205,135,7])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3648#usize 3680#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3648#usize 3680#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [110,140,14,207,117,61,1,50,35,2,166,51,143,145,85,104,230,62,135,43,183,242,18,192,131,122,184,244,45,205,135,7])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3648).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41351).take 32)=(encodeState (JGc_TX2_HashBytes.state [110,140,14,207,117,61,1,50,35,2,166,51,143,145,85,104,230,62,135,43,183,242,18,192,131,122,184,244,45,205,135,7])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3648#usize 3680#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [110,140,14,207,117,61,1,50,35,2,166,51,143,145,85,104,230,62,135,43,183,242,18,192,131,122,184,244,45,205,135,7])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [110,140,14,207,117,61,1,50,35,2,166,51,143,145,85,104,230,62,135,43,183,242,18,192,131,122,184,244,45,205,135,7]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [110,140,14,207,117,61,1,50,35,2,166,51,143,145,85,104,230,62,135,43,183,242,18,192,131,122,184,244,45,205,135,7])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      3680#usize 3712#usize)=ok (encodeState (JGc_TX2_HashBytes.state [141,64,232,71,157,231,216,45,93,159,181,117,153,193,198,18,181,64,29,202,192,123,128,152,11,184,100,22,94,163,139,202])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3680#usize 3712#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3680#usize 3712#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [141,64,232,71,157,231,216,45,93,159,181,117,153,193,198,18,181,64,29,202,192,123,128,152,11,184,100,22,94,163,139,202])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3680).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41383).take 32)=(encodeState (JGc_TX2_HashBytes.state [141,64,232,71,157,231,216,45,93,159,181,117,153,193,198,18,181,64,29,202,192,123,128,152,11,184,100,22,94,163,139,202])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3680#usize 3712#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [141,64,232,71,157,231,216,45,93,159,181,117,153,193,198,18,181,64,29,202,192,123,128,152,11,184,100,22,94,163,139,202])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [141,64,232,71,157,231,216,45,93,159,181,117,153,193,198,18,181,64,29,202,192,123,128,152,11,184,100,22,94,163,139,202]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [141,64,232,71,157,231,216,45,93,159,181,117,153,193,198,18,181,64,29,202,192,123,128,152,11,184,100,22,94,163,139,202])).property];decide)
  exact same ▸ run
#print axioms read04
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3616) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3712 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3616 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 4#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3616 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value119) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3616 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3616#usize := UScalar.eq_of_val_eq v00.at_eq
  have rn00 : Array.index_usize (s00 s).idx 1#usize=ok (4#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s00 s) indices00 values00 3616 v00 1#usize (by decide)
  have rr00 : Array.index_usize (s00 s).val 1#usize=ok (encodeState value120) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3616 v00 1#usize (by decide)
  have selected00 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes2 0#usize 0#usize 1#usize 2#usize 4#u32
    (encodeState value119) (encodeState value120) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (1:Nat)<(s00 s).n.val;rw [v00.size];decide)
    rn00 rr00 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 2#usize 1#usize) := by
    rw [selected00]
    rw [cursor00]
    exact JGy_Gu_ParentCalls2.source126 D hash (s00 s) 2#usize 3616#usize 4#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3616 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3616 v00
      4#u32 0#usize (encodeState value126) 3616#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 2#usize=ok 9#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 3616 v01 2#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 2#usize=ok (encodeState value121) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3616 v01 2#usize (by decide)
  have active01 : 2#usize<(s01 s).n := by
    change (2:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=3616#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 3#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 3#usize=ok other ∧ other≠9#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨11#u32,JGm_TX2_View.index (s01 s) indices01 values01 3616 v01 3#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s01 s).«at» 3648#usize)=ok (encodeState (JGc_TX2_HashBytes.state [224,16,194,66,110,101,52,10,179,79,182,34,88,250,183,144,150,209,247,104,194,136,212,200,251,140,161,235,156,251,89,119])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes2 2#usize 1#usize 3#usize 3648#usize 224#usize
    9#u32 (encodeState value121) (encodeState (JGc_TX2_HashBytes.state [224,16,194,66,110,101,52,10,179,79,182,34,88,250,183,144,150,209,247,104,194,136,212,200,251,140,161,235,156,251,89,119])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read01
  simp only [show 9#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes2 2#usize 1#usize=
        ok (.Next (s02 s) 3#usize 2#usize) := by
    rw [selected01]
    exact JGy_Gu_ParentCalls2.source127 D hash (s01 s) 3#usize 3648#usize 9#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 3648 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 3616 v01
      9#u32 1#usize (encodeState value127) 3648#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 3#usize=ok 11#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 3648 v02 3#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 3#usize=ok (encodeState value122) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3648 v02 3#usize (by decide)
  have active02 : 3#usize<(s02 s).n := by
    change (3:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=3648#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 4#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 4#usize=ok other ∧ other≠11#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨12#u32,JGm_TX2_View.index (s02 s) indices02 values02 3648 v02 4#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s02 s).«at» 3680#usize)=ok (encodeState (JGc_TX2_HashBytes.state [110,140,14,207,117,61,1,50,35,2,166,51,143,145,85,104,230,62,135,43,183,242,18,192,131,122,184,244,45,205,135,7])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes2 3#usize 2#usize 4#usize 3680#usize 192#usize
    11#u32 (encodeState value122) (encodeState (JGc_TX2_HashBytes.state [110,140,14,207,117,61,1,50,35,2,166,51,143,145,85,104,230,62,135,43,183,242,18,192,131,122,184,244,45,205,135,7])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read02
  simp only [show 11#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes2 3#usize 2#usize=
        ok (.Next (s03 s) 4#usize 3#usize) := by
    rw [selected02]
    exact JGy_Gu_ParentCalls2.source128 D hash (s02 s) 4#usize 3680#usize 11#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 3680 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 3648 v02
      11#u32 2#usize (encodeState value128) 3680#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 4#usize=ok 12#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 3680 v03 4#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 4#usize=ok (encodeState value123) :=
    JGm_TX2_View.value (s03 s) indices03 values03 3680 v03 4#usize (by decide)
  have active03 : 4#usize<(s03 s).n := by
    change (4:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=3680#usize := UScalar.eq_of_val_eq v03.at_eq
  have rn03 : Array.index_usize (s03 s).idx 5#usize=ok (12#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s03 s) indices03 values03 3680 v03 5#usize (by decide)
  have rr03 : Array.index_usize (s03 s).val 5#usize=ok (encodeState value124) :=
    JGm_TX2_View.value (s03 s) indices03 values03 3680 v03 5#usize (by decide)
  have selected03 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes2 4#usize 3#usize 5#usize 6#usize 12#u32
    (encodeState value123) (encodeState value124) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (5:Nat)<(s03 s).n.val;rw [v03.size];decide)
    rn03 rr03 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes2 4#usize 3#usize=
        ok (.Next (s04 s) 6#usize 4#usize) := by
    rw [selected03]
    rw [cursor03]
    exact JGy_Gu_ParentCalls2.source129 D hash (s03 s) 6#usize 3680#usize 12#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 3680 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 3680 v03
      12#u32 3#usize (encodeState value129) 3680#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 6#usize=ok 15#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 3680 v04 6#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 6#usize=ok (encodeState value125) :=
    JGm_TX2_View.value (s04 s) indices04 values04 3680 v04 6#usize (by decide)
  have active04 : 6#usize<(s04 s).n := by
    change (6:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=3680#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 7#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 7#usize=ok other ∧ other≠15#u32 ^^^ 1#u32 := by
    intro more
    change (7:Nat)<(s04 s).n.val at more
    rw [v04.size] at more
    exact False.elim ((by decide : ¬(7:Nat)<7) more)
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s04 s).«at» 3712#usize)=ok (encodeState (JGc_TX2_HashBytes.state [141,64,232,71,157,231,216,45,93,159,181,117,153,193,198,18,181,64,29,202,192,123,128,152,11,184,100,22,94,163,139,202])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes2 6#usize 4#usize 7#usize 3712#usize 160#usize
    15#u32 (encodeState value125) (encodeState (JGc_TX2_HashBytes.state [141,64,232,71,157,231,216,45,93,159,181,117,153,193,198,18,181,64,29,202,192,123,128,152,11,184,100,22,94,163,139,202])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read04
  simp only [show 15#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes2 6#usize 4#usize=
        ok (.Next (s05 s) 7#usize 5#usize) := by
    rw [selected04]
    exact JGy_Gu_ParentCalls2.source130 D hash (s04 s) 7#usize 3712#usize 15#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 3712 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 3680 v04
      15#u32 4#usize (encodeState value130) 3712#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes2 2#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes2 3#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes2 4#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes2 6#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes2 7#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s05 s).n.val≤7;rw [v05.size];decide)
  · exact JGm_TX2_View.finish (s05 s) indices05 values05 3712
      v05 5#usize (by decide)
#print axioms source
end AspisR1.JGy_Gu_Level2_12
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JGy_Gu_Level2_13
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGy_Gr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes2
def indices00 : List U32 := [2#u32,4#u32,5#u32,6#u32,7#u32]
def values00 : List (Array U8 32#usize) := [encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 2#u32 0#usize (encodeState value131) 3744#usize
 def indices01 : List U32 := [1#u32,4#u32,5#u32,6#u32,7#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value131,encodeState value127,encodeState value128,encodeState value129,encodeState value130]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 4#u32 1#usize (encodeState value132) 3744#usize
 def indices02 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value128,encodeState value129,encodeState value130]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 6#u32 2#usize (encodeState value133) 3744#usize
 def indices03 : List U32 := [1#u32,2#u32,3#u32,6#u32,7#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value133,encodeState value129,encodeState value130]
def output (s : reference.Scratch) : reference.Scratch := {s03 s with n:=3#usize}
 def indicesOut : List U32 := [1#u32,2#u32,3#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value133]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      3712#usize 3744#usize)=ok (encodeState (JGc_TX2_HashBytes.state [34,112,182,144,67,6,64,238,194,132,59,239,67,247,9,55,180,77,17,67,178,157,110,43,220,71,83,104,67,4,240,73])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3712#usize 3744#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3712#usize 3744#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [34,112,182,144,67,6,64,238,194,132,59,239,67,247,9,55,180,77,17,67,178,157,110,43,220,71,83,104,67,4,240,73])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3712).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41415).take 32)=(encodeState (JGc_TX2_HashBytes.state [34,112,182,144,67,6,64,238,194,132,59,239,67,247,9,55,180,77,17,67,178,157,110,43,220,71,83,104,67,4,240,73])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3712#usize 3744#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [34,112,182,144,67,6,64,238,194,132,59,239,67,247,9,55,180,77,17,67,178,157,110,43,220,71,83,104,67,4,240,73])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [34,112,182,144,67,6,64,238,194,132,59,239,67,247,9,55,180,77,17,67,178,157,110,43,220,71,83,104,67,4,240,73]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [34,112,182,144,67,6,64,238,194,132,59,239,67,247,9,55,180,77,17,67,178,157,110,43,220,71,83,104,67,4,240,73])).property];decide)
  exact same ▸ run
#print axioms read00
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3712) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3744 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3712 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 2#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3712 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value126) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3712 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3712#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠2#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨4#u32,JGm_TX2_View.index (s00 s) indices00 values00 3712 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s00 s).«at» 3744#usize)=ok (encodeState (JGc_TX2_HashBytes.state [34,112,182,144,67,6,64,238,194,132,59,239,67,247,9,55,180,77,17,67,178,157,110,43,220,71,83,104,67,4,240,73])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes2 0#usize 0#usize 1#usize 3744#usize 128#usize
    2#u32 (encodeState value126) (encodeState (JGc_TX2_HashBytes.state [34,112,182,144,67,6,64,238,194,132,59,239,67,247,9,55,180,77,17,67,178,157,110,43,220,71,83,104,67,4,240,73])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read00
  simp only [show 2#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGy_Gu_ParentCalls2.source131 D hash (s00 s) 1#usize 3744#usize 2#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3744 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3712 v00
      2#u32 0#usize (encodeState value131) 3744#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 4#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 3744 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value127) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3744 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=3744#usize := UScalar.eq_of_val_eq v01.at_eq
  have rn01 : Array.index_usize (s01 s).idx 2#usize=ok (4#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s01 s) indices01 values01 3744 v01 2#usize (by decide)
  have rr01 : Array.index_usize (s01 s).val 2#usize=ok (encodeState value128) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3744 v01 2#usize (by decide)
  have selected01 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes2 1#usize 1#usize 2#usize 3#usize 4#u32
    (encodeState value127) (encodeState value128) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (2:Nat)<(s01 s).n.val;rw [v01.size];decide)
    rn01 rr01 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 3#usize 2#usize) := by
    rw [selected01]
    rw [cursor01]
    exact JGy_Gu_ParentCalls2.source132 D hash (s01 s) 3#usize 3744#usize 4#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 3744 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 3744 v01
      4#u32 1#usize (encodeState value132) 3744#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 3#usize=ok 6#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 3744 v02 3#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 3#usize=ok (encodeState value129) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3744 v02 3#usize (by decide)
  have active02 : 3#usize<(s02 s).n := by
    change (3:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=3744#usize := UScalar.eq_of_val_eq v02.at_eq
  have rn02 : Array.index_usize (s02 s).idx 4#usize=ok (6#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s02 s) indices02 values02 3744 v02 4#usize (by decide)
  have rr02 : Array.index_usize (s02 s).val 4#usize=ok (encodeState value130) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3744 v02 4#usize (by decide)
  have selected02 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes2 3#usize 2#usize 4#usize 5#usize 6#u32
    (encodeState value129) (encodeState value130) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (4:Nat)<(s02 s).n.val;rw [v02.size];decide)
    rn02 rr02 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes2 3#usize 2#usize=
        ok (.Next (s03 s) 5#usize 3#usize) := by
    rw [selected02]
    rw [cursor02]
    exact JGy_Gu_ParentCalls2.source133 D hash (s02 s) 5#usize 3744#usize 6#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 3744 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 3744 v02
      6#u32 2#usize (encodeState value133) 3744#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes2 3#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes2 5#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s03 s).n.val≤5;rw [v03.size];decide)
  · exact JGm_TX2_View.finish (s03 s) indices03 values03 3744
      v03 3#usize (by decide)
#print axioms source
end AspisR1.JGy_Gu_Level2_13
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JGy_Gu_Level2_14
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGy_Gr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes2
def indices00 : List U32 := [1#u32,2#u32,3#u32]
def values00 : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value133]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 1#u32 0#usize (encodeState value134) 3776#usize
 def indices01 : List U32 := [0#u32,2#u32,3#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value134,encodeState value132,encodeState value133]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 2#u32 1#usize (encodeState value135) 3776#usize
 def indices02 : List U32 := [0#u32,1#u32,3#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value134,encodeState value135,encodeState value133]
def output (s : reference.Scratch) : reference.Scratch := {s02 s with n:=2#usize}
 def indicesOut : List U32 := [0#u32,1#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value134,encodeState value135]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      3744#usize 3776#usize)=ok (encodeState (JGc_TX2_HashBytes.state [28,133,8,205,254,15,139,95,248,58,225,38,64,117,236,147,74,140,165,149,219,239,213,12,183,184,40,0,97,10,83,26])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3744#usize 3776#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3744#usize 3776#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [28,133,8,205,254,15,139,95,248,58,225,38,64,117,236,147,74,140,165,149,219,239,213,12,183,184,40,0,97,10,83,26])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3744).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41447).take 32)=(encodeState (JGc_TX2_HashBytes.state [28,133,8,205,254,15,139,95,248,58,225,38,64,117,236,147,74,140,165,149,219,239,213,12,183,184,40,0,97,10,83,26])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3744#usize 3776#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [28,133,8,205,254,15,139,95,248,58,225,38,64,117,236,147,74,140,165,149,219,239,213,12,183,184,40,0,97,10,83,26])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [28,133,8,205,254,15,139,95,248,58,225,38,64,117,236,147,74,140,165,149,219,239,213,12,183,184,40,0,97,10,83,26]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [28,133,8,205,254,15,139,95,248,58,225,38,64,117,236,147,74,140,165,149,219,239,213,12,183,184,40,0,97,10,83,26])).property];decide)
  exact same ▸ run
#print axioms read00
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3744) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3776 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3744 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 1#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3744 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value131) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3744 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3744#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠1#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2#u32,JGm_TX2_View.index (s00 s) indices00 values00 3744 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s00 s).«at» 3776#usize)=ok (encodeState (JGc_TX2_HashBytes.state [28,133,8,205,254,15,139,95,248,58,225,38,64,117,236,147,74,140,165,149,219,239,213,12,183,184,40,0,97,10,83,26])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes2 0#usize 0#usize 1#usize 3776#usize 96#usize
    1#u32 (encodeState value131) (encodeState (JGc_TX2_HashBytes.state [28,133,8,205,254,15,139,95,248,58,225,38,64,117,236,147,74,140,165,149,219,239,213,12,183,184,40,0,97,10,83,26])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read00
  simp only [show 1#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGy_Gu_ParentCalls2.source134 D hash (s00 s) 1#usize 3776#usize 1#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3776 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3744 v00
      1#u32 0#usize (encodeState value134) 3776#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 2#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 3776 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value132) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3776 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=3776#usize := UScalar.eq_of_val_eq v01.at_eq
  have rn01 : Array.index_usize (s01 s).idx 2#usize=ok (2#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s01 s) indices01 values01 3776 v01 2#usize (by decide)
  have rr01 : Array.index_usize (s01 s).val 2#usize=ok (encodeState value133) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3776 v01 2#usize (by decide)
  have selected01 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes2 1#usize 1#usize 2#usize 3#usize 2#u32
    (encodeState value132) (encodeState value133) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (2:Nat)<(s01 s).n.val;rw [v01.size];decide)
    rn01 rr01 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 3#usize 2#usize) := by
    rw [selected01]
    rw [cursor01]
    exact JGy_Gu_ParentCalls2.source135 D hash (s01 s) 3#usize 3776#usize 2#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 3776 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 3776 v01
      2#u32 1#usize (encodeState value135) 3776#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes2 3#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s02 s).n.val≤3;rw [v02.size];decide)
  · exact JGm_TX2_View.finish (s02 s) indices02 values02 3776
      v02 2#usize (by decide)
#print axioms source
end AspisR1.JGy_Gu_Level2_14
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JGy_Gu_Level2_15
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGy_Gr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes2
def indices00 : List U32 := [0#u32,1#u32]
def values00 : List (Array U8 32#usize) := [encodeState value134,encodeState value135]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 0#u32 0#usize (encodeState value136) 3776#usize
 def indices01 : List U32 := [0#u32,1#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value136,encodeState value135]
def output (s : reference.Scratch) : reference.Scratch := {s01 s with n:=1#usize}
 def indicesOut : List U32 := [0#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value136]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3776) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3776 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3776 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3776 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value134) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3776 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3776#usize := UScalar.eq_of_val_eq v00.at_eq
  have rn00 : Array.index_usize (s00 s).idx 1#usize=ok (0#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s00 s) indices00 values00 3776 v00 1#usize (by decide)
  have rr00 : Array.index_usize (s00 s).val 1#usize=ok (encodeState value135) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3776 v00 1#usize (by decide)
  have selected00 := JGy_G_JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes2 0#usize 0#usize 1#usize 2#usize 0#u32
    (encodeState value134) (encodeState value135) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (1:Nat)<(s00 s).n.val;rw [v00.size];decide)
    rn00 rr00 (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 2#usize 1#usize) := by
    rw [selected00]
    rw [cursor00]
    exact JGy_Gu_ParentCalls2.source136 D hash (s00 s) 2#usize 3776#usize 0#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3776 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3776 v00
      0#u32 0#usize (encodeState value136) 3776#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes2 2#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s01 s).n.val≤2;rw [v01.size];decide)
  · exact JGm_TX2_View.finish (s01 s) indices01 values01 3776
      v01 1#usize (by decide)
#print axioms source
end AspisR1.JGy_Gu_Level2_15
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JGy_Gu_Level2_16
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGy_Gr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes2
def indices00 : List U32 := [0#u32]
def values00 : List (Array U8 32#usize) := [encodeState value136]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 0#u32 0#usize (encodeState value137) 3808#usize
 def indices01 : List U32 := [0#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value137]
def output (s : reference.Scratch) : reference.Scratch := {s01 s with n:=1#usize}
 def indicesOut : List U32 := [0#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value137]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      3776#usize 3808#usize)=ok (encodeState (JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3776#usize 3808#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3776#usize 3808#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3776).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41479).take 32)=(encodeState (JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3776#usize 3808#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136])).property];decide)
  exact same ▸ run
#print axioms read00
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3776) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3808 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3776 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3776 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value136) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3776 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3776#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠0#u32 ^^^ 1#u32 := by
    intro more
    change (1:Nat)<(s00 s).n.val at more
    rw [v00.size] at more
    exact False.elim ((by decide : ¬(1:Nat)<1) more)
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s00 s).«at» 3808#usize)=ok (encodeState (JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes2 0#usize 0#usize 1#usize 3808#usize 64#usize
    0#u32 (encodeState value136) (encodeState (JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read00
  simp only [show 0#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGy_Gu_ParentCalls2.source137 D hash (s00 s) 1#usize 3808#usize 0#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3808 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3776 v00
      0#u32 0#usize (encodeState value137) 3808#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s01 s).n.val≤1;rw [v01.size];decide)
  · exact JGm_TX2_View.finish (s01 s) indices01 values01 3808
      v01 1#usize (by decide)
#print axioms source
end AspisR1.JGy_Gu_Level2_16
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JGy_Gu_Level2_17
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGy_Gr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes2
def indices00 : List U32 := [0#u32]
def values00 : List (Array U8 32#usize) := [encodeState value137]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 0#u32 0#usize (encodeState value138) 3840#usize
 def indices01 : List U32 := [0#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value138]
def output (s : reference.Scratch) : reference.Scratch := {s01 s with n:=1#usize}
 def indicesOut : List U32 := [0#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value138]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      3808#usize 3840#usize)=ok (encodeState (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3808#usize 3840#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3808#usize 3840#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3808).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41511).take 32)=(encodeState (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3808#usize 3840#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80])).property];decide)
  exact same ▸ run
#print axioms read00
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3808) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3840 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3808 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3808 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value137) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3808 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3808#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠0#u32 ^^^ 1#u32 := by
    intro more
    change (1:Nat)<(s00 s).n.val at more
    rw [v00.size] at more
    exact False.elim ((by decide : ¬(1:Nat)<1) more)
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s00 s).«at» 3840#usize)=ok (encodeState (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes2 0#usize 0#usize 1#usize 3840#usize 32#usize
    0#u32 (encodeState value137) (encodeState (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read00
  simp only [show 0#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGy_Gu_ParentCalls2.source138 D hash (s00 s) 1#usize 3840#usize 0#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3840 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3808 v00
      0#u32 0#usize (encodeState value138) 3840#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s01 s).n.val≤1;rw [v01.size];decide)
  · exact JGm_TX2_View.finish (s01 s) indices01 values01 3840
      v01 1#usize (by decide)
#print axioms source
end AspisR1.JGy_Gu_Level2_17
end
