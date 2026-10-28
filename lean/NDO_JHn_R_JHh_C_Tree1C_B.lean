import NDO_JHn_R_JHh_C_Tree1C_A
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
namespace AspisR1.JHh_C_Gu_Level1_09
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [128#u32,182#u32,288#u32,312#u32,359#u32,375#u32,377#u32,408#u32,423#u32,480#u32]
def values00 : List (Array U8 32#usize) := [encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095,encodeState value096,encodeState value097,encodeState value098,encodeState value099]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 128#u32 0#usize (encodeState value100) 2912#usize
 def indices01 : List U32 := [64#u32,182#u32,288#u32,312#u32,359#u32,375#u32,377#u32,408#u32,423#u32,480#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value100,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095,encodeState value096,encodeState value097,encodeState value098,encodeState value099]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 182#u32 1#usize (encodeState value101) 2944#usize
 def indices02 : List U32 := [64#u32,91#u32,288#u32,312#u32,359#u32,375#u32,377#u32,408#u32,423#u32,480#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value100,encodeState value101,encodeState value092,encodeState value093,encodeState value094,encodeState value095,encodeState value096,encodeState value097,encodeState value098,encodeState value099]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 288#u32 2#usize (encodeState value102) 2976#usize
 def indices03 : List U32 := [64#u32,91#u32,144#u32,312#u32,359#u32,375#u32,377#u32,408#u32,423#u32,480#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value100,encodeState value101,encodeState value102,encodeState value093,encodeState value094,encodeState value095,encodeState value096,encodeState value097,encodeState value098,encodeState value099]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 312#u32 3#usize (encodeState value103) 3008#usize
 def indices04 : List U32 := [64#u32,91#u32,144#u32,156#u32,359#u32,375#u32,377#u32,408#u32,423#u32,480#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value094,encodeState value095,encodeState value096,encodeState value097,encodeState value098,encodeState value099]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 359#u32 4#usize (encodeState value104) 3040#usize
 def indices05 : List U32 := [64#u32,91#u32,144#u32,156#u32,179#u32,375#u32,377#u32,408#u32,423#u32,480#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value095,encodeState value096,encodeState value097,encodeState value098,encodeState value099]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 375#u32 5#usize (encodeState value105) 3072#usize
 def indices06 : List U32 := [64#u32,91#u32,144#u32,156#u32,179#u32,187#u32,377#u32,408#u32,423#u32,480#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value096,encodeState value097,encodeState value098,encodeState value099]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 377#u32 6#usize (encodeState value106) 3104#usize
 def indices07 : List U32 := [64#u32,91#u32,144#u32,156#u32,179#u32,187#u32,188#u32,408#u32,423#u32,480#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value097,encodeState value098,encodeState value099]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 408#u32 7#usize (encodeState value107) 3136#usize
 def indices08 : List U32 := [64#u32,91#u32,144#u32,156#u32,179#u32,187#u32,188#u32,204#u32,423#u32,480#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107,encodeState value098,encodeState value099]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 423#u32 8#usize (encodeState value108) 3168#usize
 def indices09 : List U32 := [64#u32,91#u32,144#u32,156#u32,179#u32,187#u32,188#u32,204#u32,211#u32,480#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value099]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 480#u32 9#usize (encodeState value109) 3200#usize
 def indices10 : List U32 := [64#u32,91#u32,144#u32,156#u32,179#u32,187#u32,188#u32,204#u32,211#u32,240#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [64#u32,91#u32,144#u32,156#u32,179#u32,187#u32,188#u32,204#u32,211#u32,240#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2880#usize 2912#usize)=ok (encodeState (JGc_TX2_HashBytes.state [48,144,64,126,184,85,210,61,78,213,35,254,51,10,65,79,191,48,120,196,152,221,171,137,62,2,237,75,217,230,114,206])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2880#usize 2912#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2880#usize 2912#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [48,144,64,126,184,85,210,61,78,213,35,254,51,10,65,79,191,48,120,196,152,221,171,137,62,2,237,75,217,230,114,206])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2880).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35911).take 32)=(encodeState (JGc_TX2_HashBytes.state [48,144,64,126,184,85,210,61,78,213,35,254,51,10,65,79,191,48,120,196,152,221,171,137,62,2,237,75,217,230,114,206])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2880#usize 2912#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [48,144,64,126,184,85,210,61,78,213,35,254,51,10,65,79,191,48,120,196,152,221,171,137,62,2,237,75,217,230,114,206])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [48,144,64,126,184,85,210,61,78,213,35,254,51,10,65,79,191,48,120,196,152,221,171,137,62,2,237,75,217,230,114,206]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [48,144,64,126,184,85,210,61,78,213,35,254,51,10,65,79,191,48,120,196,152,221,171,137,62,2,237,75,217,230,114,206])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2912#usize 2944#usize)=ok (encodeState (JGc_TX2_HashBytes.state [123,212,65,220,227,135,165,48,10,14,134,81,223,111,216,95,122,145,181,204,233,74,243,55,228,195,231,198,242,45,195,116])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2912#usize 2944#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2912#usize 2944#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [123,212,65,220,227,135,165,48,10,14,134,81,223,111,216,95,122,145,181,204,233,74,243,55,228,195,231,198,242,45,195,116])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2912).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35943).take 32)=(encodeState (JGc_TX2_HashBytes.state [123,212,65,220,227,135,165,48,10,14,134,81,223,111,216,95,122,145,181,204,233,74,243,55,228,195,231,198,242,45,195,116])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2912#usize 2944#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [123,212,65,220,227,135,165,48,10,14,134,81,223,111,216,95,122,145,181,204,233,74,243,55,228,195,231,198,242,45,195,116])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [123,212,65,220,227,135,165,48,10,14,134,81,223,111,216,95,122,145,181,204,233,74,243,55,228,195,231,198,242,45,195,116]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [123,212,65,220,227,135,165,48,10,14,134,81,223,111,216,95,122,145,181,204,233,74,243,55,228,195,231,198,242,45,195,116])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2944#usize 2976#usize)=ok (encodeState (JGc_TX2_HashBytes.state [105,41,192,88,96,73,217,61,90,149,168,78,2,247,208,1,169,49,116,37,15,146,137,252,165,203,84,179,141,144,47,178])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2944#usize 2976#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2944#usize 2976#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [105,41,192,88,96,73,217,61,90,149,168,78,2,247,208,1,169,49,116,37,15,146,137,252,165,203,84,179,141,144,47,178])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2944).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 35975).take 32)=(encodeState (JGc_TX2_HashBytes.state [105,41,192,88,96,73,217,61,90,149,168,78,2,247,208,1,169,49,116,37,15,146,137,252,165,203,84,179,141,144,47,178])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2944#usize 2976#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [105,41,192,88,96,73,217,61,90,149,168,78,2,247,208,1,169,49,116,37,15,146,137,252,165,203,84,179,141,144,47,178])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [105,41,192,88,96,73,217,61,90,149,168,78,2,247,208,1,169,49,116,37,15,146,137,252,165,203,84,179,141,144,47,178]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [105,41,192,88,96,73,217,61,90,149,168,78,2,247,208,1,169,49,116,37,15,146,137,252,165,203,84,179,141,144,47,178])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      2976#usize 3008#usize)=ok (encodeState (JGc_TX2_HashBytes.state [79,110,16,129,18,10,88,204,205,7,170,254,146,27,10,217,216,101,182,33,32,114,45,207,91,16,141,146,44,147,169,198])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 2976#usize 3008#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 2976#usize 3008#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [79,110,16,129,18,10,88,204,205,7,170,254,146,27,10,217,216,101,182,33,32,114,45,207,91,16,141,146,44,147,169,198])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 2976).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36007).take 32)=(encodeState (JGc_TX2_HashBytes.state [79,110,16,129,18,10,88,204,205,7,170,254,146,27,10,217,216,101,182,33,32,114,45,207,91,16,141,146,44,147,169,198])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 2976#usize 3008#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [79,110,16,129,18,10,88,204,205,7,170,254,146,27,10,217,216,101,182,33,32,114,45,207,91,16,141,146,44,147,169,198])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [79,110,16,129,18,10,88,204,205,7,170,254,146,27,10,217,216,101,182,33,32,114,45,207,91,16,141,146,44,147,169,198]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [79,110,16,129,18,10,88,204,205,7,170,254,146,27,10,217,216,101,182,33,32,114,45,207,91,16,141,146,44,147,169,198])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3008#usize 3040#usize)=ok (encodeState (JGc_TX2_HashBytes.state [11,211,99,36,92,115,16,181,114,150,174,18,232,7,212,203,202,159,103,225,65,179,95,167,92,166,67,145,5,238,42,44])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3008#usize 3040#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3008#usize 3040#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [11,211,99,36,92,115,16,181,114,150,174,18,232,7,212,203,202,159,103,225,65,179,95,167,92,166,67,145,5,238,42,44])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3008).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36039).take 32)=(encodeState (JGc_TX2_HashBytes.state [11,211,99,36,92,115,16,181,114,150,174,18,232,7,212,203,202,159,103,225,65,179,95,167,92,166,67,145,5,238,42,44])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3008#usize 3040#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [11,211,99,36,92,115,16,181,114,150,174,18,232,7,212,203,202,159,103,225,65,179,95,167,92,166,67,145,5,238,42,44])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [11,211,99,36,92,115,16,181,114,150,174,18,232,7,212,203,202,159,103,225,65,179,95,167,92,166,67,145,5,238,42,44]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [11,211,99,36,92,115,16,181,114,150,174,18,232,7,212,203,202,159,103,225,65,179,95,167,92,166,67,145,5,238,42,44])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3040#usize 3072#usize)=ok (encodeState (JGc_TX2_HashBytes.state [208,162,139,184,71,32,217,179,68,248,58,170,4,146,236,236,84,29,218,63,17,10,25,168,216,57,163,181,19,17,253,247])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3040#usize 3072#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3040#usize 3072#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [208,162,139,184,71,32,217,179,68,248,58,170,4,146,236,236,84,29,218,63,17,10,25,168,216,57,163,181,19,17,253,247])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3040).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36071).take 32)=(encodeState (JGc_TX2_HashBytes.state [208,162,139,184,71,32,217,179,68,248,58,170,4,146,236,236,84,29,218,63,17,10,25,168,216,57,163,181,19,17,253,247])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3040#usize 3072#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [208,162,139,184,71,32,217,179,68,248,58,170,4,146,236,236,84,29,218,63,17,10,25,168,216,57,163,181,19,17,253,247])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [208,162,139,184,71,32,217,179,68,248,58,170,4,146,236,236,84,29,218,63,17,10,25,168,216,57,163,181,19,17,253,247]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [208,162,139,184,71,32,217,179,68,248,58,170,4,146,236,236,84,29,218,63,17,10,25,168,216,57,163,181,19,17,253,247])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3072#usize 3104#usize)=ok (encodeState (JGc_TX2_HashBytes.state [60,103,59,209,113,130,229,235,243,97,45,115,125,45,43,4,217,213,119,152,92,68,200,106,165,187,222,51,4,211,153,18])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3072#usize 3104#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3072#usize 3104#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [60,103,59,209,113,130,229,235,243,97,45,115,125,45,43,4,217,213,119,152,92,68,200,106,165,187,222,51,4,211,153,18])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3072).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36103).take 32)=(encodeState (JGc_TX2_HashBytes.state [60,103,59,209,113,130,229,235,243,97,45,115,125,45,43,4,217,213,119,152,92,68,200,106,165,187,222,51,4,211,153,18])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3072#usize 3104#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [60,103,59,209,113,130,229,235,243,97,45,115,125,45,43,4,217,213,119,152,92,68,200,106,165,187,222,51,4,211,153,18])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [60,103,59,209,113,130,229,235,243,97,45,115,125,45,43,4,217,213,119,152,92,68,200,106,165,187,222,51,4,211,153,18]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [60,103,59,209,113,130,229,235,243,97,45,115,125,45,43,4,217,213,119,152,92,68,200,106,165,187,222,51,4,211,153,18])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3104#usize 3136#usize)=ok (encodeState (JGc_TX2_HashBytes.state [19,72,36,207,19,187,133,44,138,222,148,125,141,146,17,59,41,212,119,158,223,201,152,145,76,37,91,48,226,129,30,9])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3104#usize 3136#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3104#usize 3136#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [19,72,36,207,19,187,133,44,138,222,148,125,141,146,17,59,41,212,119,158,223,201,152,145,76,37,91,48,226,129,30,9])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3104).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36135).take 32)=(encodeState (JGc_TX2_HashBytes.state [19,72,36,207,19,187,133,44,138,222,148,125,141,146,17,59,41,212,119,158,223,201,152,145,76,37,91,48,226,129,30,9])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3104#usize 3136#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [19,72,36,207,19,187,133,44,138,222,148,125,141,146,17,59,41,212,119,158,223,201,152,145,76,37,91,48,226,129,30,9])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [19,72,36,207,19,187,133,44,138,222,148,125,141,146,17,59,41,212,119,158,223,201,152,145,76,37,91,48,226,129,30,9]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [19,72,36,207,19,187,133,44,138,222,148,125,141,146,17,59,41,212,119,158,223,201,152,145,76,37,91,48,226,129,30,9])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3136#usize 3168#usize)=ok (encodeState (JGc_TX2_HashBytes.state [186,33,168,206,73,137,127,197,84,223,139,201,20,128,251,0,154,250,60,123,141,245,74,52,213,26,143,116,98,102,120,146])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3136#usize 3168#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3136#usize 3168#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [186,33,168,206,73,137,127,197,84,223,139,201,20,128,251,0,154,250,60,123,141,245,74,52,213,26,143,116,98,102,120,146])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3136).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36167).take 32)=(encodeState (JGc_TX2_HashBytes.state [186,33,168,206,73,137,127,197,84,223,139,201,20,128,251,0,154,250,60,123,141,245,74,52,213,26,143,116,98,102,120,146])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3136#usize 3168#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [186,33,168,206,73,137,127,197,84,223,139,201,20,128,251,0,154,250,60,123,141,245,74,52,213,26,143,116,98,102,120,146])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [186,33,168,206,73,137,127,197,84,223,139,201,20,128,251,0,154,250,60,123,141,245,74,52,213,26,143,116,98,102,120,146]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [186,33,168,206,73,137,127,197,84,223,139,201,20,128,251,0,154,250,60,123,141,245,74,52,213,26,143,116,98,102,120,146])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3168#usize 3200#usize)=ok (encodeState (JGc_TX2_HashBytes.state [58,64,20,28,188,224,199,55,182,135,197,202,243,225,130,75,187,86,96,87,139,220,144,34,26,247,190,0,220,86,80,95])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3168#usize 3200#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3168#usize 3200#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [58,64,20,28,188,224,199,55,182,135,197,202,243,225,130,75,187,86,96,87,139,220,144,34,26,247,190,0,220,86,80,95])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3168).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36199).take 32)=(encodeState (JGc_TX2_HashBytes.state [58,64,20,28,188,224,199,55,182,135,197,202,243,225,130,75,187,86,96,87,139,220,144,34,26,247,190,0,220,86,80,95])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3168#usize 3200#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [58,64,20,28,188,224,199,55,182,135,197,202,243,225,130,75,187,86,96,87,139,220,144,34,26,247,190,0,220,86,80,95])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [58,64,20,28,188,224,199,55,182,135,197,202,243,225,130,75,187,86,96,87,139,220,144,34,26,247,190,0,220,86,80,95]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [58,64,20,28,188,224,199,55,182,135,197,202,243,225,130,75,187,86,96,87,139,220,144,34,26,247,190,0,220,86,80,95])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 2880) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3200 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 2880 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 128#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 2880 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value090) :=
    JGm_TX2_View.value (s00 s) indices00 values00 2880 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=2880#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠128#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨182#u32,JGm_TX2_View.index (s00 s) indices00 values00 2880 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 2912#usize)=ok (encodeState (JGc_TX2_HashBytes.state [48,144,64,126,184,85,210,61,78,213,35,254,51,10,65,79,191,48,120,196,152,221,171,137,62,2,237,75,217,230,114,206])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 2912#usize 1536#usize
    128#u32 (encodeState value090) (encodeState (JGc_TX2_HashBytes.state [48,144,64,126,184,85,210,61,78,213,35,254,51,10,65,79,191,48,120,196,152,221,171,137,62,2,237,75,217,230,114,206])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 128#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source100 D hash (s00 s) 1#usize 2912#usize 128#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 2912 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 2880 v00
      128#u32 0#usize (encodeState value100) 2912#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 182#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 2912 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value091) :=
    JGm_TX2_View.value (s01 s) indices01 values01 2912 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=2912#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠182#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨288#u32,JGm_TX2_View.index (s01 s) indices01 values01 2912 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 2944#usize)=ok (encodeState (JGc_TX2_HashBytes.state [123,212,65,220,227,135,165,48,10,14,134,81,223,111,216,95,122,145,181,204,233,74,243,55,228,195,231,198,242,45,195,116])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 2944#usize 1504#usize
    182#u32 (encodeState value091) (encodeState (JGc_TX2_HashBytes.state [123,212,65,220,227,135,165,48,10,14,134,81,223,111,216,95,122,145,181,204,233,74,243,55,228,195,231,198,242,45,195,116])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 182#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source101 D hash (s01 s) 2#usize 2944#usize 182#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 2944 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 2912 v01
      182#u32 1#usize (encodeState value101) 2944#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 288#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 2944 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value092) :=
    JGm_TX2_View.value (s02 s) indices02 values02 2944 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=2944#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠288#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨312#u32,JGm_TX2_View.index (s02 s) indices02 values02 2944 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s02 s).«at» 2976#usize)=ok (encodeState (JGc_TX2_HashBytes.state [105,41,192,88,96,73,217,61,90,149,168,78,2,247,208,1,169,49,116,37,15,146,137,252,165,203,84,179,141,144,47,178])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 2#usize 3#usize 2976#usize 1472#usize
    288#u32 (encodeState value092) (encodeState (JGc_TX2_HashBytes.state [105,41,192,88,96,73,217,61,90,149,168,78,2,247,208,1,169,49,116,37,15,146,137,252,165,203,84,179,141,144,47,178])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read02
  simp only [show 288#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls1.source102 D hash (s02 s) 3#usize 2976#usize 288#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 2976 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 2944 v02
      288#u32 2#usize (encodeState value102) 2976#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 312#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 2976 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value093) :=
    JGm_TX2_View.value (s03 s) indices03 values03 2976 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=2976#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠312#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨359#u32,JGm_TX2_View.index (s03 s) indices03 values03 2976 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s03 s).«at» 3008#usize)=ok (encodeState (JGc_TX2_HashBytes.state [79,110,16,129,18,10,88,204,205,7,170,254,146,27,10,217,216,101,182,33,32,114,45,207,91,16,141,146,44,147,169,198])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 3#usize 4#usize 3008#usize 1440#usize
    312#u32 (encodeState value093) (encodeState (JGc_TX2_HashBytes.state [79,110,16,129,18,10,88,204,205,7,170,254,146,27,10,217,216,101,182,33,32,114,45,207,91,16,141,146,44,147,169,198])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read03
  simp only [show 312#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls1.source103 D hash (s03 s) 4#usize 3008#usize 312#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 3008 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 2976 v03
      312#u32 3#usize (encodeState value103) 3008#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 359#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 3008 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value094) :=
    JGm_TX2_View.value (s04 s) indices04 values04 3008 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=3008#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠359#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨375#u32,JGm_TX2_View.index (s04 s) indices04 values04 3008 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 3040#usize)=ok (encodeState (JGc_TX2_HashBytes.state [11,211,99,36,92,115,16,181,114,150,174,18,232,7,212,203,202,159,103,225,65,179,95,167,92,166,67,145,5,238,42,44])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 4#usize 5#usize 3040#usize 1408#usize
    359#u32 (encodeState value094) (encodeState (JGc_TX2_HashBytes.state [11,211,99,36,92,115,16,181,114,150,174,18,232,7,212,203,202,159,103,225,65,179,95,167,92,166,67,145,5,238,42,44])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 359#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source104 D hash (s04 s) 5#usize 3040#usize 359#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 3040 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 3008 v04
      359#u32 4#usize (encodeState value104) 3040#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 375#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 3040 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value095) :=
    JGm_TX2_View.value (s05 s) indices05 values05 3040 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=3040#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠375#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨377#u32,JGm_TX2_View.index (s05 s) indices05 values05 3040 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s05 s).«at» 3072#usize)=ok (encodeState (JGc_TX2_HashBytes.state [208,162,139,184,71,32,217,179,68,248,58,170,4,146,236,236,84,29,218,63,17,10,25,168,216,57,163,181,19,17,253,247])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes1 5#usize 5#usize 6#usize 3072#usize 1376#usize
    375#u32 (encodeState value095) (encodeState (JGc_TX2_HashBytes.state [208,162,139,184,71,32,217,179,68,248,58,170,4,146,236,236,84,29,218,63,17,10,25,168,216,57,163,181,19,17,253,247])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read05
  simp only [show 375#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls1.source105 D hash (s05 s) 6#usize 3072#usize 375#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 3072 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 3040 v05
      375#u32 5#usize (encodeState value105) 3072#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 377#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 3072 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value096) :=
    JGm_TX2_View.value (s06 s) indices06 values06 3072 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=3072#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠377#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨408#u32,JGm_TX2_View.index (s06 s) indices06 values06 3072 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s06 s).«at» 3104#usize)=ok (encodeState (JGc_TX2_HashBytes.state [60,103,59,209,113,130,229,235,243,97,45,115,125,45,43,4,217,213,119,152,92,68,200,106,165,187,222,51,4,211,153,18])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes1 6#usize 6#usize 7#usize 3104#usize 1344#usize
    377#u32 (encodeState value096) (encodeState (JGc_TX2_HashBytes.state [60,103,59,209,113,130,229,235,243,97,45,115,125,45,43,4,217,213,119,152,92,68,200,106,165,187,222,51,4,211,153,18])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read06
  simp only [show 377#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls1.source106 D hash (s06 s) 7#usize 3104#usize 377#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 3104 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 3072 v06
      377#u32 6#usize (encodeState value106) 3104#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 408#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 3104 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value097) :=
    JGm_TX2_View.value (s07 s) indices07 values07 3104 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=3104#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠408#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨423#u32,JGm_TX2_View.index (s07 s) indices07 values07 3104 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s07 s).«at» 3136#usize)=ok (encodeState (JGc_TX2_HashBytes.state [19,72,36,207,19,187,133,44,138,222,148,125,141,146,17,59,41,212,119,158,223,201,152,145,76,37,91,48,226,129,30,9])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes1 7#usize 7#usize 8#usize 3136#usize 1312#usize
    408#u32 (encodeState value097) (encodeState (JGc_TX2_HashBytes.state [19,72,36,207,19,187,133,44,138,222,148,125,141,146,17,59,41,212,119,158,223,201,152,145,76,37,91,48,226,129,30,9])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read07
  simp only [show 408#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls1.source107 D hash (s07 s) 8#usize 3136#usize 408#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 3136 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 3104 v07
      408#u32 7#usize (encodeState value107) 3136#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 423#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 3136 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value098) :=
    JGm_TX2_View.value (s08 s) indices08 values08 3136 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=3136#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠423#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨480#u32,JGm_TX2_View.index (s08 s) indices08 values08 3136 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s08 s).«at» 3168#usize)=ok (encodeState (JGc_TX2_HashBytes.state [186,33,168,206,73,137,127,197,84,223,139,201,20,128,251,0,154,250,60,123,141,245,74,52,213,26,143,116,98,102,120,146])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes1 8#usize 8#usize 9#usize 3168#usize 1280#usize
    423#u32 (encodeState value098) (encodeState (JGc_TX2_HashBytes.state [186,33,168,206,73,137,127,197,84,223,139,201,20,128,251,0,154,250,60,123,141,245,74,52,213,26,143,116,98,102,120,146])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read08
  simp only [show 423#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls1.source108 D hash (s08 s) 9#usize 3168#usize 423#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 3168 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 3136 v08
      423#u32 8#usize (encodeState value108) 3168#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 480#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 3168 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value099) :=
    JGm_TX2_View.value (s09 s) indices09 values09 3168 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=3168#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠480#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s09 s).«at» 3200#usize)=ok (encodeState (JGc_TX2_HashBytes.state [58,64,20,28,188,224,199,55,182,135,197,202,243,225,130,75,187,86,96,87,139,220,144,34,26,247,190,0,220,86,80,95])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes1 9#usize 9#usize 10#usize 3200#usize 1248#usize
    480#u32 (encodeState value099) (encodeState (JGc_TX2_HashBytes.state [58,64,20,28,188,224,199,55,182,135,197,202,243,225,130,75,187,86,96,87,139,220,144,34,26,247,190,0,220,86,80,95])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read09
  simp only [show 480#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls1.source109 D hash (s09 s) 10#usize 3200#usize 480#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 3200 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 3168 v09
      480#u32 9#usize (encodeState value109) 3200#usize (by decide)
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
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 3200
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_09
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_10
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [64#u32,91#u32,144#u32,156#u32,179#u32,187#u32,188#u32,204#u32,211#u32,240#u32]
def values00 : List (Array U8 32#usize) := [encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 64#u32 0#usize (encodeState value110) 3232#usize
 def indices01 : List U32 := [32#u32,91#u32,144#u32,156#u32,179#u32,187#u32,188#u32,204#u32,211#u32,240#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value110,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 91#u32 1#usize (encodeState value111) 3264#usize
 def indices02 : List U32 := [32#u32,45#u32,144#u32,156#u32,179#u32,187#u32,188#u32,204#u32,211#u32,240#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 144#u32 2#usize (encodeState value112) 3296#usize
 def indices03 : List U32 := [32#u32,45#u32,72#u32,156#u32,179#u32,187#u32,188#u32,204#u32,211#u32,240#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 156#u32 3#usize (encodeState value113) 3328#usize
 def indices04 : List U32 := [32#u32,45#u32,72#u32,78#u32,179#u32,187#u32,188#u32,204#u32,211#u32,240#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value104,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 179#u32 4#usize (encodeState value114) 3360#usize
 def indices05 : List U32 := [32#u32,45#u32,72#u32,78#u32,89#u32,187#u32,188#u32,204#u32,211#u32,240#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 187#u32 5#usize (encodeState value115) 3392#usize
 def indices06 : List U32 := [32#u32,45#u32,72#u32,78#u32,89#u32,93#u32,188#u32,204#u32,211#u32,240#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 188#u32 6#usize (encodeState value116) 3424#usize
 def indices07 : List U32 := [32#u32,45#u32,72#u32,78#u32,89#u32,93#u32,94#u32,204#u32,211#u32,240#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value107,encodeState value108,encodeState value109]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 204#u32 7#usize (encodeState value117) 3456#usize
 def indices08 : List U32 := [32#u32,45#u32,72#u32,78#u32,89#u32,93#u32,94#u32,102#u32,211#u32,240#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value108,encodeState value109]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 211#u32 8#usize (encodeState value118) 3488#usize
 def indices09 : List U32 := [32#u32,45#u32,72#u32,78#u32,89#u32,93#u32,94#u32,102#u32,105#u32,240#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value109]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 240#u32 9#usize (encodeState value119) 3520#usize
 def indices10 : List U32 := [32#u32,45#u32,72#u32,78#u32,89#u32,93#u32,94#u32,102#u32,105#u32,120#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [32#u32,45#u32,72#u32,78#u32,89#u32,93#u32,94#u32,102#u32,105#u32,120#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3200#usize 3232#usize)=ok (encodeState (JGc_TX2_HashBytes.state [64,93,241,125,70,107,252,101,30,148,14,215,74,250,227,182,249,65,129,42,162,101,220,242,179,42,5,160,220,31,103,150])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3200#usize 3232#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3200#usize 3232#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [64,93,241,125,70,107,252,101,30,148,14,215,74,250,227,182,249,65,129,42,162,101,220,242,179,42,5,160,220,31,103,150])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3200).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36231).take 32)=(encodeState (JGc_TX2_HashBytes.state [64,93,241,125,70,107,252,101,30,148,14,215,74,250,227,182,249,65,129,42,162,101,220,242,179,42,5,160,220,31,103,150])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3200#usize 3232#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [64,93,241,125,70,107,252,101,30,148,14,215,74,250,227,182,249,65,129,42,162,101,220,242,179,42,5,160,220,31,103,150])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [64,93,241,125,70,107,252,101,30,148,14,215,74,250,227,182,249,65,129,42,162,101,220,242,179,42,5,160,220,31,103,150]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [64,93,241,125,70,107,252,101,30,148,14,215,74,250,227,182,249,65,129,42,162,101,220,242,179,42,5,160,220,31,103,150])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3232#usize 3264#usize)=ok (encodeState (JGc_TX2_HashBytes.state [198,65,48,63,241,221,71,5,120,194,136,208,90,35,236,55,212,20,152,28,68,68,108,189,66,188,78,237,91,99,244,231])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3232#usize 3264#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3232#usize 3264#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [198,65,48,63,241,221,71,5,120,194,136,208,90,35,236,55,212,20,152,28,68,68,108,189,66,188,78,237,91,99,244,231])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3232).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36263).take 32)=(encodeState (JGc_TX2_HashBytes.state [198,65,48,63,241,221,71,5,120,194,136,208,90,35,236,55,212,20,152,28,68,68,108,189,66,188,78,237,91,99,244,231])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3232#usize 3264#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [198,65,48,63,241,221,71,5,120,194,136,208,90,35,236,55,212,20,152,28,68,68,108,189,66,188,78,237,91,99,244,231])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [198,65,48,63,241,221,71,5,120,194,136,208,90,35,236,55,212,20,152,28,68,68,108,189,66,188,78,237,91,99,244,231]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [198,65,48,63,241,221,71,5,120,194,136,208,90,35,236,55,212,20,152,28,68,68,108,189,66,188,78,237,91,99,244,231])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3264#usize 3296#usize)=ok (encodeState (JGc_TX2_HashBytes.state [164,41,120,158,16,43,175,133,186,191,175,18,223,41,66,159,126,137,11,165,228,232,46,160,78,239,53,218,10,204,109,142])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3264#usize 3296#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3264#usize 3296#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [164,41,120,158,16,43,175,133,186,191,175,18,223,41,66,159,126,137,11,165,228,232,46,160,78,239,53,218,10,204,109,142])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3264).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36295).take 32)=(encodeState (JGc_TX2_HashBytes.state [164,41,120,158,16,43,175,133,186,191,175,18,223,41,66,159,126,137,11,165,228,232,46,160,78,239,53,218,10,204,109,142])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3264#usize 3296#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [164,41,120,158,16,43,175,133,186,191,175,18,223,41,66,159,126,137,11,165,228,232,46,160,78,239,53,218,10,204,109,142])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [164,41,120,158,16,43,175,133,186,191,175,18,223,41,66,159,126,137,11,165,228,232,46,160,78,239,53,218,10,204,109,142]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [164,41,120,158,16,43,175,133,186,191,175,18,223,41,66,159,126,137,11,165,228,232,46,160,78,239,53,218,10,204,109,142])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3296#usize 3328#usize)=ok (encodeState (JGc_TX2_HashBytes.state [100,11,72,203,23,49,116,82,9,97,40,39,67,176,85,179,239,78,31,49,180,135,233,14,182,133,146,114,96,7,47,39])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3296#usize 3328#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3296#usize 3328#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [100,11,72,203,23,49,116,82,9,97,40,39,67,176,85,179,239,78,31,49,180,135,233,14,182,133,146,114,96,7,47,39])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3296).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36327).take 32)=(encodeState (JGc_TX2_HashBytes.state [100,11,72,203,23,49,116,82,9,97,40,39,67,176,85,179,239,78,31,49,180,135,233,14,182,133,146,114,96,7,47,39])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3296#usize 3328#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [100,11,72,203,23,49,116,82,9,97,40,39,67,176,85,179,239,78,31,49,180,135,233,14,182,133,146,114,96,7,47,39])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [100,11,72,203,23,49,116,82,9,97,40,39,67,176,85,179,239,78,31,49,180,135,233,14,182,133,146,114,96,7,47,39]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [100,11,72,203,23,49,116,82,9,97,40,39,67,176,85,179,239,78,31,49,180,135,233,14,182,133,146,114,96,7,47,39])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3328#usize 3360#usize)=ok (encodeState (JGc_TX2_HashBytes.state [184,18,54,84,108,157,180,156,80,20,210,100,117,102,246,78,234,211,56,215,194,254,92,204,54,91,195,240,221,94,111,149])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3328#usize 3360#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3328#usize 3360#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [184,18,54,84,108,157,180,156,80,20,210,100,117,102,246,78,234,211,56,215,194,254,92,204,54,91,195,240,221,94,111,149])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3328).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36359).take 32)=(encodeState (JGc_TX2_HashBytes.state [184,18,54,84,108,157,180,156,80,20,210,100,117,102,246,78,234,211,56,215,194,254,92,204,54,91,195,240,221,94,111,149])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3328#usize 3360#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [184,18,54,84,108,157,180,156,80,20,210,100,117,102,246,78,234,211,56,215,194,254,92,204,54,91,195,240,221,94,111,149])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [184,18,54,84,108,157,180,156,80,20,210,100,117,102,246,78,234,211,56,215,194,254,92,204,54,91,195,240,221,94,111,149]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [184,18,54,84,108,157,180,156,80,20,210,100,117,102,246,78,234,211,56,215,194,254,92,204,54,91,195,240,221,94,111,149])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3360#usize 3392#usize)=ok (encodeState (JGc_TX2_HashBytes.state [63,228,40,85,211,28,242,188,32,35,226,36,237,119,146,127,123,57,188,62,64,103,16,217,15,240,231,101,242,238,216,229])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3360#usize 3392#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3360#usize 3392#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [63,228,40,85,211,28,242,188,32,35,226,36,237,119,146,127,123,57,188,62,64,103,16,217,15,240,231,101,242,238,216,229])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3360).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36391).take 32)=(encodeState (JGc_TX2_HashBytes.state [63,228,40,85,211,28,242,188,32,35,226,36,237,119,146,127,123,57,188,62,64,103,16,217,15,240,231,101,242,238,216,229])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3360#usize 3392#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [63,228,40,85,211,28,242,188,32,35,226,36,237,119,146,127,123,57,188,62,64,103,16,217,15,240,231,101,242,238,216,229])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [63,228,40,85,211,28,242,188,32,35,226,36,237,119,146,127,123,57,188,62,64,103,16,217,15,240,231,101,242,238,216,229]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [63,228,40,85,211,28,242,188,32,35,226,36,237,119,146,127,123,57,188,62,64,103,16,217,15,240,231,101,242,238,216,229])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3392#usize 3424#usize)=ok (encodeState (JGc_TX2_HashBytes.state [130,69,10,242,115,118,110,253,30,219,254,90,113,163,245,178,100,145,233,86,77,1,166,132,100,215,190,224,34,250,87,35])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3392#usize 3424#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3392#usize 3424#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [130,69,10,242,115,118,110,253,30,219,254,90,113,163,245,178,100,145,233,86,77,1,166,132,100,215,190,224,34,250,87,35])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3392).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36423).take 32)=(encodeState (JGc_TX2_HashBytes.state [130,69,10,242,115,118,110,253,30,219,254,90,113,163,245,178,100,145,233,86,77,1,166,132,100,215,190,224,34,250,87,35])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3392#usize 3424#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [130,69,10,242,115,118,110,253,30,219,254,90,113,163,245,178,100,145,233,86,77,1,166,132,100,215,190,224,34,250,87,35])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [130,69,10,242,115,118,110,253,30,219,254,90,113,163,245,178,100,145,233,86,77,1,166,132,100,215,190,224,34,250,87,35]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [130,69,10,242,115,118,110,253,30,219,254,90,113,163,245,178,100,145,233,86,77,1,166,132,100,215,190,224,34,250,87,35])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3424#usize 3456#usize)=ok (encodeState (JGc_TX2_HashBytes.state [112,24,125,244,37,57,3,138,146,193,211,93,237,176,196,152,131,55,166,189,57,218,132,5,116,252,78,158,63,50,109,12])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3424#usize 3456#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3424#usize 3456#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [112,24,125,244,37,57,3,138,146,193,211,93,237,176,196,152,131,55,166,189,57,218,132,5,116,252,78,158,63,50,109,12])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3424).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36455).take 32)=(encodeState (JGc_TX2_HashBytes.state [112,24,125,244,37,57,3,138,146,193,211,93,237,176,196,152,131,55,166,189,57,218,132,5,116,252,78,158,63,50,109,12])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3424#usize 3456#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [112,24,125,244,37,57,3,138,146,193,211,93,237,176,196,152,131,55,166,189,57,218,132,5,116,252,78,158,63,50,109,12])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [112,24,125,244,37,57,3,138,146,193,211,93,237,176,196,152,131,55,166,189,57,218,132,5,116,252,78,158,63,50,109,12]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [112,24,125,244,37,57,3,138,146,193,211,93,237,176,196,152,131,55,166,189,57,218,132,5,116,252,78,158,63,50,109,12])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3456#usize 3488#usize)=ok (encodeState (JGc_TX2_HashBytes.state [215,230,177,31,18,107,67,128,173,64,143,244,114,180,207,188,65,56,143,94,43,60,198,20,173,93,12,193,37,52,52,140])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3456#usize 3488#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3456#usize 3488#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [215,230,177,31,18,107,67,128,173,64,143,244,114,180,207,188,65,56,143,94,43,60,198,20,173,93,12,193,37,52,52,140])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3456).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36487).take 32)=(encodeState (JGc_TX2_HashBytes.state [215,230,177,31,18,107,67,128,173,64,143,244,114,180,207,188,65,56,143,94,43,60,198,20,173,93,12,193,37,52,52,140])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3456#usize 3488#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [215,230,177,31,18,107,67,128,173,64,143,244,114,180,207,188,65,56,143,94,43,60,198,20,173,93,12,193,37,52,52,140])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [215,230,177,31,18,107,67,128,173,64,143,244,114,180,207,188,65,56,143,94,43,60,198,20,173,93,12,193,37,52,52,140]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [215,230,177,31,18,107,67,128,173,64,143,244,114,180,207,188,65,56,143,94,43,60,198,20,173,93,12,193,37,52,52,140])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3488#usize 3520#usize)=ok (encodeState (JGc_TX2_HashBytes.state [103,164,167,122,243,231,22,164,230,111,87,102,49,233,9,71,238,122,34,122,154,242,71,9,153,52,13,204,21,144,129,141])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3488#usize 3520#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3488#usize 3520#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [103,164,167,122,243,231,22,164,230,111,87,102,49,233,9,71,238,122,34,122,154,242,71,9,153,52,13,204,21,144,129,141])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3488).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36519).take 32)=(encodeState (JGc_TX2_HashBytes.state [103,164,167,122,243,231,22,164,230,111,87,102,49,233,9,71,238,122,34,122,154,242,71,9,153,52,13,204,21,144,129,141])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3488#usize 3520#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [103,164,167,122,243,231,22,164,230,111,87,102,49,233,9,71,238,122,34,122,154,242,71,9,153,52,13,204,21,144,129,141])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [103,164,167,122,243,231,22,164,230,111,87,102,49,233,9,71,238,122,34,122,154,242,71,9,153,52,13,204,21,144,129,141]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [103,164,167,122,243,231,22,164,230,111,87,102,49,233,9,71,238,122,34,122,154,242,71,9,153,52,13,204,21,144,129,141])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3200) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3520 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3200 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 64#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3200 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value100) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3200 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3200#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠64#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨91#u32,JGm_TX2_View.index (s00 s) indices00 values00 3200 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 3232#usize)=ok (encodeState (JGc_TX2_HashBytes.state [64,93,241,125,70,107,252,101,30,148,14,215,74,250,227,182,249,65,129,42,162,101,220,242,179,42,5,160,220,31,103,150])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 3232#usize 1216#usize
    64#u32 (encodeState value100) (encodeState (JGc_TX2_HashBytes.state [64,93,241,125,70,107,252,101,30,148,14,215,74,250,227,182,249,65,129,42,162,101,220,242,179,42,5,160,220,31,103,150])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 64#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source110 D hash (s00 s) 1#usize 3232#usize 64#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3232 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3200 v00
      64#u32 0#usize (encodeState value110) 3232#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 91#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 3232 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value101) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3232 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=3232#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠91#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨144#u32,JGm_TX2_View.index (s01 s) indices01 values01 3232 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 3264#usize)=ok (encodeState (JGc_TX2_HashBytes.state [198,65,48,63,241,221,71,5,120,194,136,208,90,35,236,55,212,20,152,28,68,68,108,189,66,188,78,237,91,99,244,231])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 3264#usize 1184#usize
    91#u32 (encodeState value101) (encodeState (JGc_TX2_HashBytes.state [198,65,48,63,241,221,71,5,120,194,136,208,90,35,236,55,212,20,152,28,68,68,108,189,66,188,78,237,91,99,244,231])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 91#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source111 D hash (s01 s) 2#usize 3264#usize 91#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 3264 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 3232 v01
      91#u32 1#usize (encodeState value111) 3264#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 144#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 3264 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value102) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3264 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=3264#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠144#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨156#u32,JGm_TX2_View.index (s02 s) indices02 values02 3264 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s02 s).«at» 3296#usize)=ok (encodeState (JGc_TX2_HashBytes.state [164,41,120,158,16,43,175,133,186,191,175,18,223,41,66,159,126,137,11,165,228,232,46,160,78,239,53,218,10,204,109,142])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 2#usize 3#usize 3296#usize 1152#usize
    144#u32 (encodeState value102) (encodeState (JGc_TX2_HashBytes.state [164,41,120,158,16,43,175,133,186,191,175,18,223,41,66,159,126,137,11,165,228,232,46,160,78,239,53,218,10,204,109,142])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read02
  simp only [show 144#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls1.source112 D hash (s02 s) 3#usize 3296#usize 144#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 3296 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 3264 v02
      144#u32 2#usize (encodeState value112) 3296#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 156#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 3296 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value103) :=
    JGm_TX2_View.value (s03 s) indices03 values03 3296 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=3296#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠156#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨179#u32,JGm_TX2_View.index (s03 s) indices03 values03 3296 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s03 s).«at» 3328#usize)=ok (encodeState (JGc_TX2_HashBytes.state [100,11,72,203,23,49,116,82,9,97,40,39,67,176,85,179,239,78,31,49,180,135,233,14,182,133,146,114,96,7,47,39])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 3#usize 4#usize 3328#usize 1120#usize
    156#u32 (encodeState value103) (encodeState (JGc_TX2_HashBytes.state [100,11,72,203,23,49,116,82,9,97,40,39,67,176,85,179,239,78,31,49,180,135,233,14,182,133,146,114,96,7,47,39])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read03
  simp only [show 156#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls1.source113 D hash (s03 s) 4#usize 3328#usize 156#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 3328 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 3296 v03
      156#u32 3#usize (encodeState value113) 3328#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 179#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 3328 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value104) :=
    JGm_TX2_View.value (s04 s) indices04 values04 3328 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=3328#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠179#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨187#u32,JGm_TX2_View.index (s04 s) indices04 values04 3328 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 3360#usize)=ok (encodeState (JGc_TX2_HashBytes.state [184,18,54,84,108,157,180,156,80,20,210,100,117,102,246,78,234,211,56,215,194,254,92,204,54,91,195,240,221,94,111,149])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 4#usize 5#usize 3360#usize 1088#usize
    179#u32 (encodeState value104) (encodeState (JGc_TX2_HashBytes.state [184,18,54,84,108,157,180,156,80,20,210,100,117,102,246,78,234,211,56,215,194,254,92,204,54,91,195,240,221,94,111,149])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 179#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source114 D hash (s04 s) 5#usize 3360#usize 179#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 3360 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 3328 v04
      179#u32 4#usize (encodeState value114) 3360#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 187#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 3360 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value105) :=
    JGm_TX2_View.value (s05 s) indices05 values05 3360 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=3360#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠187#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨188#u32,JGm_TX2_View.index (s05 s) indices05 values05 3360 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s05 s).«at» 3392#usize)=ok (encodeState (JGc_TX2_HashBytes.state [63,228,40,85,211,28,242,188,32,35,226,36,237,119,146,127,123,57,188,62,64,103,16,217,15,240,231,101,242,238,216,229])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes1 5#usize 5#usize 6#usize 3392#usize 1056#usize
    187#u32 (encodeState value105) (encodeState (JGc_TX2_HashBytes.state [63,228,40,85,211,28,242,188,32,35,226,36,237,119,146,127,123,57,188,62,64,103,16,217,15,240,231,101,242,238,216,229])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read05
  simp only [show 187#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls1.source115 D hash (s05 s) 6#usize 3392#usize 187#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 3392 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 3360 v05
      187#u32 5#usize (encodeState value115) 3392#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 188#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 3392 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value106) :=
    JGm_TX2_View.value (s06 s) indices06 values06 3392 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=3392#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠188#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨204#u32,JGm_TX2_View.index (s06 s) indices06 values06 3392 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s06 s).«at» 3424#usize)=ok (encodeState (JGc_TX2_HashBytes.state [130,69,10,242,115,118,110,253,30,219,254,90,113,163,245,178,100,145,233,86,77,1,166,132,100,215,190,224,34,250,87,35])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes1 6#usize 6#usize 7#usize 3424#usize 1024#usize
    188#u32 (encodeState value106) (encodeState (JGc_TX2_HashBytes.state [130,69,10,242,115,118,110,253,30,219,254,90,113,163,245,178,100,145,233,86,77,1,166,132,100,215,190,224,34,250,87,35])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read06
  simp only [show 188#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls1.source116 D hash (s06 s) 7#usize 3424#usize 188#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 3424 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 3392 v06
      188#u32 6#usize (encodeState value116) 3424#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 204#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 3424 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value107) :=
    JGm_TX2_View.value (s07 s) indices07 values07 3424 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=3424#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠204#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨211#u32,JGm_TX2_View.index (s07 s) indices07 values07 3424 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s07 s).«at» 3456#usize)=ok (encodeState (JGc_TX2_HashBytes.state [112,24,125,244,37,57,3,138,146,193,211,93,237,176,196,152,131,55,166,189,57,218,132,5,116,252,78,158,63,50,109,12])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes1 7#usize 7#usize 8#usize 3456#usize 992#usize
    204#u32 (encodeState value107) (encodeState (JGc_TX2_HashBytes.state [112,24,125,244,37,57,3,138,146,193,211,93,237,176,196,152,131,55,166,189,57,218,132,5,116,252,78,158,63,50,109,12])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read07
  simp only [show 204#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls1.source117 D hash (s07 s) 8#usize 3456#usize 204#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 3456 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 3424 v07
      204#u32 7#usize (encodeState value117) 3456#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 211#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 3456 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value108) :=
    JGm_TX2_View.value (s08 s) indices08 values08 3456 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=3456#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠211#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨240#u32,JGm_TX2_View.index (s08 s) indices08 values08 3456 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s08 s).«at» 3488#usize)=ok (encodeState (JGc_TX2_HashBytes.state [215,230,177,31,18,107,67,128,173,64,143,244,114,180,207,188,65,56,143,94,43,60,198,20,173,93,12,193,37,52,52,140])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes1 8#usize 8#usize 9#usize 3488#usize 960#usize
    211#u32 (encodeState value108) (encodeState (JGc_TX2_HashBytes.state [215,230,177,31,18,107,67,128,173,64,143,244,114,180,207,188,65,56,143,94,43,60,198,20,173,93,12,193,37,52,52,140])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read08
  simp only [show 211#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls1.source118 D hash (s08 s) 9#usize 3488#usize 211#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 3488 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 3456 v08
      211#u32 8#usize (encodeState value118) 3488#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 240#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 3488 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value109) :=
    JGm_TX2_View.value (s09 s) indices09 values09 3488 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=3488#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠240#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s09 s).«at» 3520#usize)=ok (encodeState (JGc_TX2_HashBytes.state [103,164,167,122,243,231,22,164,230,111,87,102,49,233,9,71,238,122,34,122,154,242,71,9,153,52,13,204,21,144,129,141])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes1 9#usize 9#usize 10#usize 3520#usize 928#usize
    240#u32 (encodeState value109) (encodeState (JGc_TX2_HashBytes.state [103,164,167,122,243,231,22,164,230,111,87,102,49,233,9,71,238,122,34,122,154,242,71,9,153,52,13,204,21,144,129,141])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read09
  simp only [show 240#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls1.source119 D hash (s09 s) 10#usize 3520#usize 240#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 3520 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 3488 v09
      240#u32 9#usize (encodeState value119) 3520#usize (by decide)
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
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 3520
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_10
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_11
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [32#u32,45#u32,72#u32,78#u32,89#u32,93#u32,94#u32,102#u32,105#u32,120#u32]
def values00 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 32#u32 0#usize (encodeState value120) 3552#usize
 def indices01 : List U32 := [16#u32,45#u32,72#u32,78#u32,89#u32,93#u32,94#u32,102#u32,105#u32,120#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value120,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 45#u32 1#usize (encodeState value121) 3584#usize
 def indices02 : List U32 := [16#u32,22#u32,72#u32,78#u32,89#u32,93#u32,94#u32,102#u32,105#u32,120#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 72#u32 2#usize (encodeState value122) 3616#usize
 def indices03 : List U32 := [16#u32,22#u32,36#u32,78#u32,89#u32,93#u32,94#u32,102#u32,105#u32,120#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 78#u32 3#usize (encodeState value123) 3648#usize
 def indices04 : List U32 := [16#u32,22#u32,36#u32,39#u32,89#u32,93#u32,94#u32,102#u32,105#u32,120#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 89#u32 4#usize (encodeState value124) 3680#usize
 def indices05 : List U32 := [16#u32,22#u32,36#u32,39#u32,44#u32,93#u32,94#u32,102#u32,105#u32,120#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 93#u32 5#usize (encodeState value125) 3712#usize
 def indices06 : List U32 := [16#u32,22#u32,36#u32,39#u32,44#u32,46#u32,94#u32,102#u32,105#u32,120#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 94#u32 6#usize (encodeState value126) 3744#usize
 def indices07 : List U32 := [16#u32,22#u32,36#u32,39#u32,44#u32,46#u32,47#u32,102#u32,105#u32,120#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value117,encodeState value118,encodeState value119]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 102#u32 7#usize (encodeState value127) 3776#usize
 def indices08 : List U32 := [16#u32,22#u32,36#u32,39#u32,44#u32,46#u32,47#u32,51#u32,105#u32,120#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value118,encodeState value119]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 105#u32 8#usize (encodeState value128) 3808#usize
 def indices09 : List U32 := [16#u32,22#u32,36#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,120#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value119]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 120#u32 9#usize (encodeState value129) 3840#usize
 def indices10 : List U32 := [16#u32,22#u32,36#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [16#u32,22#u32,36#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3520#usize 3552#usize)=ok (encodeState (JGc_TX2_HashBytes.state [217,175,196,100,106,166,4,160,30,133,139,241,21,195,125,114,222,108,239,37,188,97,229,163,164,197,201,14,71,43,175,9])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3520#usize 3552#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3520#usize 3552#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [217,175,196,100,106,166,4,160,30,133,139,241,21,195,125,114,222,108,239,37,188,97,229,163,164,197,201,14,71,43,175,9])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3520).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36551).take 32)=(encodeState (JGc_TX2_HashBytes.state [217,175,196,100,106,166,4,160,30,133,139,241,21,195,125,114,222,108,239,37,188,97,229,163,164,197,201,14,71,43,175,9])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3520#usize 3552#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [217,175,196,100,106,166,4,160,30,133,139,241,21,195,125,114,222,108,239,37,188,97,229,163,164,197,201,14,71,43,175,9])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [217,175,196,100,106,166,4,160,30,133,139,241,21,195,125,114,222,108,239,37,188,97,229,163,164,197,201,14,71,43,175,9]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [217,175,196,100,106,166,4,160,30,133,139,241,21,195,125,114,222,108,239,37,188,97,229,163,164,197,201,14,71,43,175,9])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3552#usize 3584#usize)=ok (encodeState (JGc_TX2_HashBytes.state [245,86,191,21,128,168,40,91,146,136,112,192,222,80,59,237,196,147,226,240,168,112,253,192,150,7,143,51,196,9,248,37])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3552#usize 3584#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3552#usize 3584#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [245,86,191,21,128,168,40,91,146,136,112,192,222,80,59,237,196,147,226,240,168,112,253,192,150,7,143,51,196,9,248,37])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3552).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36583).take 32)=(encodeState (JGc_TX2_HashBytes.state [245,86,191,21,128,168,40,91,146,136,112,192,222,80,59,237,196,147,226,240,168,112,253,192,150,7,143,51,196,9,248,37])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3552#usize 3584#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [245,86,191,21,128,168,40,91,146,136,112,192,222,80,59,237,196,147,226,240,168,112,253,192,150,7,143,51,196,9,248,37])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [245,86,191,21,128,168,40,91,146,136,112,192,222,80,59,237,196,147,226,240,168,112,253,192,150,7,143,51,196,9,248,37]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [245,86,191,21,128,168,40,91,146,136,112,192,222,80,59,237,196,147,226,240,168,112,253,192,150,7,143,51,196,9,248,37])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3584#usize 3616#usize)=ok (encodeState (JGc_TX2_HashBytes.state [211,15,11,17,227,198,215,231,129,25,99,34,247,62,244,155,62,104,100,207,187,196,141,130,8,193,86,21,253,129,202,143])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3584#usize 3616#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3584#usize 3616#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [211,15,11,17,227,198,215,231,129,25,99,34,247,62,244,155,62,104,100,207,187,196,141,130,8,193,86,21,253,129,202,143])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3584).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36615).take 32)=(encodeState (JGc_TX2_HashBytes.state [211,15,11,17,227,198,215,231,129,25,99,34,247,62,244,155,62,104,100,207,187,196,141,130,8,193,86,21,253,129,202,143])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3584#usize 3616#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [211,15,11,17,227,198,215,231,129,25,99,34,247,62,244,155,62,104,100,207,187,196,141,130,8,193,86,21,253,129,202,143])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [211,15,11,17,227,198,215,231,129,25,99,34,247,62,244,155,62,104,100,207,187,196,141,130,8,193,86,21,253,129,202,143]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [211,15,11,17,227,198,215,231,129,25,99,34,247,62,244,155,62,104,100,207,187,196,141,130,8,193,86,21,253,129,202,143])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3616#usize 3648#usize)=ok (encodeState (JGc_TX2_HashBytes.state [15,101,120,74,113,3,178,205,140,1,22,242,63,68,171,18,163,88,82,90,84,49,24,53,10,48,240,86,180,229,195,57])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3616#usize 3648#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3616#usize 3648#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [15,101,120,74,113,3,178,205,140,1,22,242,63,68,171,18,163,88,82,90,84,49,24,53,10,48,240,86,180,229,195,57])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3616).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36647).take 32)=(encodeState (JGc_TX2_HashBytes.state [15,101,120,74,113,3,178,205,140,1,22,242,63,68,171,18,163,88,82,90,84,49,24,53,10,48,240,86,180,229,195,57])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3616#usize 3648#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [15,101,120,74,113,3,178,205,140,1,22,242,63,68,171,18,163,88,82,90,84,49,24,53,10,48,240,86,180,229,195,57])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [15,101,120,74,113,3,178,205,140,1,22,242,63,68,171,18,163,88,82,90,84,49,24,53,10,48,240,86,180,229,195,57]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [15,101,120,74,113,3,178,205,140,1,22,242,63,68,171,18,163,88,82,90,84,49,24,53,10,48,240,86,180,229,195,57])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3648#usize 3680#usize)=ok (encodeState (JGc_TX2_HashBytes.state [196,176,224,63,58,66,146,38,214,180,92,204,177,20,194,41,249,159,205,160,145,250,27,12,85,20,34,52,29,203,225,93])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3648#usize 3680#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3648#usize 3680#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [196,176,224,63,58,66,146,38,214,180,92,204,177,20,194,41,249,159,205,160,145,250,27,12,85,20,34,52,29,203,225,93])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3648).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36679).take 32)=(encodeState (JGc_TX2_HashBytes.state [196,176,224,63,58,66,146,38,214,180,92,204,177,20,194,41,249,159,205,160,145,250,27,12,85,20,34,52,29,203,225,93])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3648#usize 3680#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [196,176,224,63,58,66,146,38,214,180,92,204,177,20,194,41,249,159,205,160,145,250,27,12,85,20,34,52,29,203,225,93])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [196,176,224,63,58,66,146,38,214,180,92,204,177,20,194,41,249,159,205,160,145,250,27,12,85,20,34,52,29,203,225,93]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [196,176,224,63,58,66,146,38,214,180,92,204,177,20,194,41,249,159,205,160,145,250,27,12,85,20,34,52,29,203,225,93])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3680#usize 3712#usize)=ok (encodeState (JGc_TX2_HashBytes.state [167,124,21,206,95,202,120,7,203,62,13,33,133,95,118,113,8,86,18,144,249,35,80,206,151,128,245,184,149,62,143,89])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3680#usize 3712#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3680#usize 3712#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [167,124,21,206,95,202,120,7,203,62,13,33,133,95,118,113,8,86,18,144,249,35,80,206,151,128,245,184,149,62,143,89])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3680).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36711).take 32)=(encodeState (JGc_TX2_HashBytes.state [167,124,21,206,95,202,120,7,203,62,13,33,133,95,118,113,8,86,18,144,249,35,80,206,151,128,245,184,149,62,143,89])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3680#usize 3712#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [167,124,21,206,95,202,120,7,203,62,13,33,133,95,118,113,8,86,18,144,249,35,80,206,151,128,245,184,149,62,143,89])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [167,124,21,206,95,202,120,7,203,62,13,33,133,95,118,113,8,86,18,144,249,35,80,206,151,128,245,184,149,62,143,89]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [167,124,21,206,95,202,120,7,203,62,13,33,133,95,118,113,8,86,18,144,249,35,80,206,151,128,245,184,149,62,143,89])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3712#usize 3744#usize)=ok (encodeState (JGc_TX2_HashBytes.state [40,24,99,188,225,201,92,11,125,146,207,221,1,133,77,170,92,32,179,180,208,97,222,61,235,239,136,46,164,100,6,189])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3712#usize 3744#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3712#usize 3744#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [40,24,99,188,225,201,92,11,125,146,207,221,1,133,77,170,92,32,179,180,208,97,222,61,235,239,136,46,164,100,6,189])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3712).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36743).take 32)=(encodeState (JGc_TX2_HashBytes.state [40,24,99,188,225,201,92,11,125,146,207,221,1,133,77,170,92,32,179,180,208,97,222,61,235,239,136,46,164,100,6,189])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3712#usize 3744#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [40,24,99,188,225,201,92,11,125,146,207,221,1,133,77,170,92,32,179,180,208,97,222,61,235,239,136,46,164,100,6,189])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [40,24,99,188,225,201,92,11,125,146,207,221,1,133,77,170,92,32,179,180,208,97,222,61,235,239,136,46,164,100,6,189]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [40,24,99,188,225,201,92,11,125,146,207,221,1,133,77,170,92,32,179,180,208,97,222,61,235,239,136,46,164,100,6,189])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3744#usize 3776#usize)=ok (encodeState (JGc_TX2_HashBytes.state [108,85,77,126,24,37,128,176,24,222,208,119,252,7,77,71,162,105,159,240,41,58,2,199,0,136,85,41,86,124,234,35])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3744#usize 3776#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3744#usize 3776#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [108,85,77,126,24,37,128,176,24,222,208,119,252,7,77,71,162,105,159,240,41,58,2,199,0,136,85,41,86,124,234,35])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3744).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36775).take 32)=(encodeState (JGc_TX2_HashBytes.state [108,85,77,126,24,37,128,176,24,222,208,119,252,7,77,71,162,105,159,240,41,58,2,199,0,136,85,41,86,124,234,35])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3744#usize 3776#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [108,85,77,126,24,37,128,176,24,222,208,119,252,7,77,71,162,105,159,240,41,58,2,199,0,136,85,41,86,124,234,35])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [108,85,77,126,24,37,128,176,24,222,208,119,252,7,77,71,162,105,159,240,41,58,2,199,0,136,85,41,86,124,234,35]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [108,85,77,126,24,37,128,176,24,222,208,119,252,7,77,71,162,105,159,240,41,58,2,199,0,136,85,41,86,124,234,35])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3776#usize 3808#usize)=ok (encodeState (JGc_TX2_HashBytes.state [210,204,100,222,46,98,83,84,247,179,170,243,109,102,248,130,215,145,18,205,170,10,130,187,6,137,151,18,195,62,117,160])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3776#usize 3808#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3776#usize 3808#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [210,204,100,222,46,98,83,84,247,179,170,243,109,102,248,130,215,145,18,205,170,10,130,187,6,137,151,18,195,62,117,160])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3776).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36807).take 32)=(encodeState (JGc_TX2_HashBytes.state [210,204,100,222,46,98,83,84,247,179,170,243,109,102,248,130,215,145,18,205,170,10,130,187,6,137,151,18,195,62,117,160])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3776#usize 3808#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [210,204,100,222,46,98,83,84,247,179,170,243,109,102,248,130,215,145,18,205,170,10,130,187,6,137,151,18,195,62,117,160])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [210,204,100,222,46,98,83,84,247,179,170,243,109,102,248,130,215,145,18,205,170,10,130,187,6,137,151,18,195,62,117,160]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [210,204,100,222,46,98,83,84,247,179,170,243,109,102,248,130,215,145,18,205,170,10,130,187,6,137,151,18,195,62,117,160])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      3808#usize 3840#usize)=ok (encodeState (JGc_TX2_HashBytes.state [36,122,216,128,213,83,7,55,28,214,71,249,243,137,72,100,98,181,52,193,77,132,94,236,71,30,38,228,18,154,155,76])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 3808#usize 3840#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 3808#usize 3840#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [36,122,216,128,213,83,7,55,28,214,71,249,243,137,72,100,98,181,52,193,77,132,94,236,71,30,38,228,18,154,155,76])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 3808).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 36839).take 32)=(encodeState (JGc_TX2_HashBytes.state [36,122,216,128,213,83,7,55,28,214,71,249,243,137,72,100,98,181,52,193,77,132,94,236,71,30,38,228,18,154,155,76])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 3808#usize 3840#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [36,122,216,128,213,83,7,55,28,214,71,249,243,137,72,100,98,181,52,193,77,132,94,236,71,30,38,228,18,154,155,76])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [36,122,216,128,213,83,7,55,28,214,71,249,243,137,72,100,98,181,52,193,77,132,94,236,71,30,38,228,18,154,155,76]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [36,122,216,128,213,83,7,55,28,214,71,249,243,137,72,100,98,181,52,193,77,132,94,236,71,30,38,228,18,154,155,76])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3520) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3840 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3520 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 32#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3520 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value110) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3520 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3520#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠32#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨45#u32,JGm_TX2_View.index (s00 s) indices00 values00 3520 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 3552#usize)=ok (encodeState (JGc_TX2_HashBytes.state [217,175,196,100,106,166,4,160,30,133,139,241,21,195,125,114,222,108,239,37,188,97,229,163,164,197,201,14,71,43,175,9])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 3552#usize 896#usize
    32#u32 (encodeState value110) (encodeState (JGc_TX2_HashBytes.state [217,175,196,100,106,166,4,160,30,133,139,241,21,195,125,114,222,108,239,37,188,97,229,163,164,197,201,14,71,43,175,9])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 32#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source120 D hash (s00 s) 1#usize 3552#usize 32#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3552 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3520 v00
      32#u32 0#usize (encodeState value120) 3552#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 45#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 3552 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value111) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3552 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=3552#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠45#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨72#u32,JGm_TX2_View.index (s01 s) indices01 values01 3552 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 3584#usize)=ok (encodeState (JGc_TX2_HashBytes.state [245,86,191,21,128,168,40,91,146,136,112,192,222,80,59,237,196,147,226,240,168,112,253,192,150,7,143,51,196,9,248,37])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 3584#usize 864#usize
    45#u32 (encodeState value111) (encodeState (JGc_TX2_HashBytes.state [245,86,191,21,128,168,40,91,146,136,112,192,222,80,59,237,196,147,226,240,168,112,253,192,150,7,143,51,196,9,248,37])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 45#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source121 D hash (s01 s) 2#usize 3584#usize 45#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 3584 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 3552 v01
      45#u32 1#usize (encodeState value121) 3584#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 72#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 3584 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value112) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3584 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=3584#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠72#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨78#u32,JGm_TX2_View.index (s02 s) indices02 values02 3584 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s02 s).«at» 3616#usize)=ok (encodeState (JGc_TX2_HashBytes.state [211,15,11,17,227,198,215,231,129,25,99,34,247,62,244,155,62,104,100,207,187,196,141,130,8,193,86,21,253,129,202,143])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 2#usize 3#usize 3616#usize 832#usize
    72#u32 (encodeState value112) (encodeState (JGc_TX2_HashBytes.state [211,15,11,17,227,198,215,231,129,25,99,34,247,62,244,155,62,104,100,207,187,196,141,130,8,193,86,21,253,129,202,143])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read02
  simp only [show 72#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls1.source122 D hash (s02 s) 3#usize 3616#usize 72#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 3616 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 3584 v02
      72#u32 2#usize (encodeState value122) 3616#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 78#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 3616 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value113) :=
    JGm_TX2_View.value (s03 s) indices03 values03 3616 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=3616#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠78#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨89#u32,JGm_TX2_View.index (s03 s) indices03 values03 3616 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s03 s).«at» 3648#usize)=ok (encodeState (JGc_TX2_HashBytes.state [15,101,120,74,113,3,178,205,140,1,22,242,63,68,171,18,163,88,82,90,84,49,24,53,10,48,240,86,180,229,195,57])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 3#usize 4#usize 3648#usize 800#usize
    78#u32 (encodeState value113) (encodeState (JGc_TX2_HashBytes.state [15,101,120,74,113,3,178,205,140,1,22,242,63,68,171,18,163,88,82,90,84,49,24,53,10,48,240,86,180,229,195,57])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read03
  simp only [show 78#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls1.source123 D hash (s03 s) 4#usize 3648#usize 78#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 3648 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 3616 v03
      78#u32 3#usize (encodeState value123) 3648#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 89#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 3648 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value114) :=
    JGm_TX2_View.value (s04 s) indices04 values04 3648 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=3648#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠89#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨93#u32,JGm_TX2_View.index (s04 s) indices04 values04 3648 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 3680#usize)=ok (encodeState (JGc_TX2_HashBytes.state [196,176,224,63,58,66,146,38,214,180,92,204,177,20,194,41,249,159,205,160,145,250,27,12,85,20,34,52,29,203,225,93])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 4#usize 5#usize 3680#usize 768#usize
    89#u32 (encodeState value114) (encodeState (JGc_TX2_HashBytes.state [196,176,224,63,58,66,146,38,214,180,92,204,177,20,194,41,249,159,205,160,145,250,27,12,85,20,34,52,29,203,225,93])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 89#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source124 D hash (s04 s) 5#usize 3680#usize 89#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 3680 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 3648 v04
      89#u32 4#usize (encodeState value124) 3680#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 93#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 3680 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value115) :=
    JGm_TX2_View.value (s05 s) indices05 values05 3680 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=3680#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠93#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨94#u32,JGm_TX2_View.index (s05 s) indices05 values05 3680 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s05 s).«at» 3712#usize)=ok (encodeState (JGc_TX2_HashBytes.state [167,124,21,206,95,202,120,7,203,62,13,33,133,95,118,113,8,86,18,144,249,35,80,206,151,128,245,184,149,62,143,89])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes1 5#usize 5#usize 6#usize 3712#usize 736#usize
    93#u32 (encodeState value115) (encodeState (JGc_TX2_HashBytes.state [167,124,21,206,95,202,120,7,203,62,13,33,133,95,118,113,8,86,18,144,249,35,80,206,151,128,245,184,149,62,143,89])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read05
  simp only [show 93#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls1.source125 D hash (s05 s) 6#usize 3712#usize 93#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 3712 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 3680 v05
      93#u32 5#usize (encodeState value125) 3712#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 94#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 3712 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value116) :=
    JGm_TX2_View.value (s06 s) indices06 values06 3712 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=3712#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠94#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨102#u32,JGm_TX2_View.index (s06 s) indices06 values06 3712 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s06 s).«at» 3744#usize)=ok (encodeState (JGc_TX2_HashBytes.state [40,24,99,188,225,201,92,11,125,146,207,221,1,133,77,170,92,32,179,180,208,97,222,61,235,239,136,46,164,100,6,189])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes1 6#usize 6#usize 7#usize 3744#usize 704#usize
    94#u32 (encodeState value116) (encodeState (JGc_TX2_HashBytes.state [40,24,99,188,225,201,92,11,125,146,207,221,1,133,77,170,92,32,179,180,208,97,222,61,235,239,136,46,164,100,6,189])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read06
  simp only [show 94#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls1.source126 D hash (s06 s) 7#usize 3744#usize 94#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 3744 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 3712 v06
      94#u32 6#usize (encodeState value126) 3744#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 102#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 3744 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value117) :=
    JGm_TX2_View.value (s07 s) indices07 values07 3744 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=3744#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠102#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨105#u32,JGm_TX2_View.index (s07 s) indices07 values07 3744 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s07 s).«at» 3776#usize)=ok (encodeState (JGc_TX2_HashBytes.state [108,85,77,126,24,37,128,176,24,222,208,119,252,7,77,71,162,105,159,240,41,58,2,199,0,136,85,41,86,124,234,35])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes1 7#usize 7#usize 8#usize 3776#usize 672#usize
    102#u32 (encodeState value117) (encodeState (JGc_TX2_HashBytes.state [108,85,77,126,24,37,128,176,24,222,208,119,252,7,77,71,162,105,159,240,41,58,2,199,0,136,85,41,86,124,234,35])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read07
  simp only [show 102#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls1.source127 D hash (s07 s) 8#usize 3776#usize 102#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 3776 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 3744 v07
      102#u32 7#usize (encodeState value127) 3776#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 105#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 3776 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value118) :=
    JGm_TX2_View.value (s08 s) indices08 values08 3776 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=3776#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠105#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨120#u32,JGm_TX2_View.index (s08 s) indices08 values08 3776 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s08 s).«at» 3808#usize)=ok (encodeState (JGc_TX2_HashBytes.state [210,204,100,222,46,98,83,84,247,179,170,243,109,102,248,130,215,145,18,205,170,10,130,187,6,137,151,18,195,62,117,160])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes1 8#usize 8#usize 9#usize 3808#usize 640#usize
    105#u32 (encodeState value118) (encodeState (JGc_TX2_HashBytes.state [210,204,100,222,46,98,83,84,247,179,170,243,109,102,248,130,215,145,18,205,170,10,130,187,6,137,151,18,195,62,117,160])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read08
  simp only [show 105#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls1.source128 D hash (s08 s) 9#usize 3808#usize 105#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 3808 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 3776 v08
      105#u32 8#usize (encodeState value128) 3808#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 120#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 3808 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value119) :=
    JGm_TX2_View.value (s09 s) indices09 values09 3808 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=3808#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠120#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s09 s).«at» 3840#usize)=ok (encodeState (JGc_TX2_HashBytes.state [36,122,216,128,213,83,7,55,28,214,71,249,243,137,72,100,98,181,52,193,77,132,94,236,71,30,38,228,18,154,155,76])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes1 9#usize 9#usize 10#usize 3840#usize 608#usize
    120#u32 (encodeState value119) (encodeState (JGc_TX2_HashBytes.state [36,122,216,128,213,83,7,55,28,214,71,249,243,137,72,100,98,181,52,193,77,132,94,236,71,30,38,228,18,154,155,76])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read09
  simp only [show 120#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls1.source129 D hash (s09 s) 10#usize 3840#usize 120#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 3840 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 3808 v09
      120#u32 9#usize (encodeState value129) 3840#usize (by decide)
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
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 3840
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_11
end


end
