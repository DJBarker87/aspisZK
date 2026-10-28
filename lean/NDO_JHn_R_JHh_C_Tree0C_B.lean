import NDO_JHn_R_JHh_C_Tree0C_A
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
namespace AspisR1.JHh_C_Gu_Level0_09
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHe_C_Gr_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes0
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
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2880#usize 2912#usize)=ok (encodeState (JGc_TX2_HashBytes.state [23,74,195,49,213,135,245,27,57,199,58,222,148,196,183,123,71,5,192,127,140,213,208,209,54,153,86,127,135,105,132,180])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2880#usize 2912#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2880#usize 2912#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [23,74,195,49,213,135,245,27,57,199,58,222,148,196,183,123,71,5,192,127,140,213,208,209,54,153,86,127,135,105,132,180])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2880).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31239).take 32)=(encodeState (JGc_TX2_HashBytes.state [23,74,195,49,213,135,245,27,57,199,58,222,148,196,183,123,71,5,192,127,140,213,208,209,54,153,86,127,135,105,132,180])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2880#usize 2912#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [23,74,195,49,213,135,245,27,57,199,58,222,148,196,183,123,71,5,192,127,140,213,208,209,54,153,86,127,135,105,132,180])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [23,74,195,49,213,135,245,27,57,199,58,222,148,196,183,123,71,5,192,127,140,213,208,209,54,153,86,127,135,105,132,180]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [23,74,195,49,213,135,245,27,57,199,58,222,148,196,183,123,71,5,192,127,140,213,208,209,54,153,86,127,135,105,132,180])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2912#usize 2944#usize)=ok (encodeState (JGc_TX2_HashBytes.state [247,170,236,136,32,227,215,1,30,170,171,104,222,196,102,119,141,43,224,250,73,121,228,110,63,169,195,18,64,55,103,111])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2912#usize 2944#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2912#usize 2944#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [247,170,236,136,32,227,215,1,30,170,171,104,222,196,102,119,141,43,224,250,73,121,228,110,63,169,195,18,64,55,103,111])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2912).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31271).take 32)=(encodeState (JGc_TX2_HashBytes.state [247,170,236,136,32,227,215,1,30,170,171,104,222,196,102,119,141,43,224,250,73,121,228,110,63,169,195,18,64,55,103,111])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2912#usize 2944#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [247,170,236,136,32,227,215,1,30,170,171,104,222,196,102,119,141,43,224,250,73,121,228,110,63,169,195,18,64,55,103,111])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [247,170,236,136,32,227,215,1,30,170,171,104,222,196,102,119,141,43,224,250,73,121,228,110,63,169,195,18,64,55,103,111]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [247,170,236,136,32,227,215,1,30,170,171,104,222,196,102,119,141,43,224,250,73,121,228,110,63,169,195,18,64,55,103,111])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2944#usize 2976#usize)=ok (encodeState (JGc_TX2_HashBytes.state [190,108,13,171,84,192,94,96,227,48,105,48,244,245,190,168,224,83,16,169,249,226,55,97,180,229,154,227,86,36,50,122])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2944#usize 2976#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2944#usize 2976#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [190,108,13,171,84,192,94,96,227,48,105,48,244,245,190,168,224,83,16,169,249,226,55,97,180,229,154,227,86,36,50,122])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2944).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31303).take 32)=(encodeState (JGc_TX2_HashBytes.state [190,108,13,171,84,192,94,96,227,48,105,48,244,245,190,168,224,83,16,169,249,226,55,97,180,229,154,227,86,36,50,122])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2944#usize 2976#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [190,108,13,171,84,192,94,96,227,48,105,48,244,245,190,168,224,83,16,169,249,226,55,97,180,229,154,227,86,36,50,122])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [190,108,13,171,84,192,94,96,227,48,105,48,244,245,190,168,224,83,16,169,249,226,55,97,180,229,154,227,86,36,50,122]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [190,108,13,171,84,192,94,96,227,48,105,48,244,245,190,168,224,83,16,169,249,226,55,97,180,229,154,227,86,36,50,122])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      2976#usize 3008#usize)=ok (encodeState (JGc_TX2_HashBytes.state [157,66,177,205,179,25,156,253,216,204,238,141,248,146,126,57,146,197,187,130,191,130,41,226,29,137,114,88,159,239,90,188])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 2976#usize 3008#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 2976#usize 3008#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [157,66,177,205,179,25,156,253,216,204,238,141,248,146,126,57,146,197,187,130,191,130,41,226,29,137,114,88,159,239,90,188])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 2976).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31335).take 32)=(encodeState (JGc_TX2_HashBytes.state [157,66,177,205,179,25,156,253,216,204,238,141,248,146,126,57,146,197,187,130,191,130,41,226,29,137,114,88,159,239,90,188])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 2976#usize 3008#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [157,66,177,205,179,25,156,253,216,204,238,141,248,146,126,57,146,197,187,130,191,130,41,226,29,137,114,88,159,239,90,188])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [157,66,177,205,179,25,156,253,216,204,238,141,248,146,126,57,146,197,187,130,191,130,41,226,29,137,114,88,159,239,90,188]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [157,66,177,205,179,25,156,253,216,204,238,141,248,146,126,57,146,197,187,130,191,130,41,226,29,137,114,88,159,239,90,188])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3008#usize 3040#usize)=ok (encodeState (JGc_TX2_HashBytes.state [79,115,19,153,165,205,224,136,61,186,168,120,162,67,201,141,134,174,172,243,21,240,241,100,42,229,53,233,153,170,42,41])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3008#usize 3040#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3008#usize 3040#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [79,115,19,153,165,205,224,136,61,186,168,120,162,67,201,141,134,174,172,243,21,240,241,100,42,229,53,233,153,170,42,41])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3008).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31367).take 32)=(encodeState (JGc_TX2_HashBytes.state [79,115,19,153,165,205,224,136,61,186,168,120,162,67,201,141,134,174,172,243,21,240,241,100,42,229,53,233,153,170,42,41])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3008#usize 3040#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [79,115,19,153,165,205,224,136,61,186,168,120,162,67,201,141,134,174,172,243,21,240,241,100,42,229,53,233,153,170,42,41])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [79,115,19,153,165,205,224,136,61,186,168,120,162,67,201,141,134,174,172,243,21,240,241,100,42,229,53,233,153,170,42,41]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [79,115,19,153,165,205,224,136,61,186,168,120,162,67,201,141,134,174,172,243,21,240,241,100,42,229,53,233,153,170,42,41])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3040#usize 3072#usize)=ok (encodeState (JGc_TX2_HashBytes.state [148,43,99,22,57,180,71,36,176,106,37,117,42,190,120,213,40,143,126,3,58,186,68,221,194,74,60,125,229,230,106,79])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3040#usize 3072#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3040#usize 3072#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [148,43,99,22,57,180,71,36,176,106,37,117,42,190,120,213,40,143,126,3,58,186,68,221,194,74,60,125,229,230,106,79])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3040).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31399).take 32)=(encodeState (JGc_TX2_HashBytes.state [148,43,99,22,57,180,71,36,176,106,37,117,42,190,120,213,40,143,126,3,58,186,68,221,194,74,60,125,229,230,106,79])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3040#usize 3072#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [148,43,99,22,57,180,71,36,176,106,37,117,42,190,120,213,40,143,126,3,58,186,68,221,194,74,60,125,229,230,106,79])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [148,43,99,22,57,180,71,36,176,106,37,117,42,190,120,213,40,143,126,3,58,186,68,221,194,74,60,125,229,230,106,79]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [148,43,99,22,57,180,71,36,176,106,37,117,42,190,120,213,40,143,126,3,58,186,68,221,194,74,60,125,229,230,106,79])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3072#usize 3104#usize)=ok (encodeState (JGc_TX2_HashBytes.state [207,102,135,191,134,26,82,182,249,62,205,164,72,118,227,234,90,100,188,183,151,160,216,216,200,245,4,24,126,19,178,5])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3072#usize 3104#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3072#usize 3104#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [207,102,135,191,134,26,82,182,249,62,205,164,72,118,227,234,90,100,188,183,151,160,216,216,200,245,4,24,126,19,178,5])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3072).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31431).take 32)=(encodeState (JGc_TX2_HashBytes.state [207,102,135,191,134,26,82,182,249,62,205,164,72,118,227,234,90,100,188,183,151,160,216,216,200,245,4,24,126,19,178,5])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3072#usize 3104#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [207,102,135,191,134,26,82,182,249,62,205,164,72,118,227,234,90,100,188,183,151,160,216,216,200,245,4,24,126,19,178,5])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [207,102,135,191,134,26,82,182,249,62,205,164,72,118,227,234,90,100,188,183,151,160,216,216,200,245,4,24,126,19,178,5]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [207,102,135,191,134,26,82,182,249,62,205,164,72,118,227,234,90,100,188,183,151,160,216,216,200,245,4,24,126,19,178,5])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3104#usize 3136#usize)=ok (encodeState (JGc_TX2_HashBytes.state [136,24,60,241,94,194,126,24,120,244,56,48,145,68,42,168,200,103,87,128,189,66,104,116,209,245,141,65,97,81,150,11])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3104#usize 3136#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3104#usize 3136#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [136,24,60,241,94,194,126,24,120,244,56,48,145,68,42,168,200,103,87,128,189,66,104,116,209,245,141,65,97,81,150,11])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3104).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31463).take 32)=(encodeState (JGc_TX2_HashBytes.state [136,24,60,241,94,194,126,24,120,244,56,48,145,68,42,168,200,103,87,128,189,66,104,116,209,245,141,65,97,81,150,11])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3104#usize 3136#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [136,24,60,241,94,194,126,24,120,244,56,48,145,68,42,168,200,103,87,128,189,66,104,116,209,245,141,65,97,81,150,11])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [136,24,60,241,94,194,126,24,120,244,56,48,145,68,42,168,200,103,87,128,189,66,104,116,209,245,141,65,97,81,150,11]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [136,24,60,241,94,194,126,24,120,244,56,48,145,68,42,168,200,103,87,128,189,66,104,116,209,245,141,65,97,81,150,11])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3136#usize 3168#usize)=ok (encodeState (JGc_TX2_HashBytes.state [236,224,3,7,229,22,125,66,186,131,47,131,187,123,43,166,14,188,255,80,197,222,226,154,83,187,231,109,201,152,99,74])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3136#usize 3168#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3136#usize 3168#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [236,224,3,7,229,22,125,66,186,131,47,131,187,123,43,166,14,188,255,80,197,222,226,154,83,187,231,109,201,152,99,74])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3136).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31495).take 32)=(encodeState (JGc_TX2_HashBytes.state [236,224,3,7,229,22,125,66,186,131,47,131,187,123,43,166,14,188,255,80,197,222,226,154,83,187,231,109,201,152,99,74])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3136#usize 3168#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [236,224,3,7,229,22,125,66,186,131,47,131,187,123,43,166,14,188,255,80,197,222,226,154,83,187,231,109,201,152,99,74])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [236,224,3,7,229,22,125,66,186,131,47,131,187,123,43,166,14,188,255,80,197,222,226,154,83,187,231,109,201,152,99,74]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [236,224,3,7,229,22,125,66,186,131,47,131,187,123,43,166,14,188,255,80,197,222,226,154,83,187,231,109,201,152,99,74])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3168#usize 3200#usize)=ok (encodeState (JGc_TX2_HashBytes.state [129,168,53,62,31,143,67,207,71,169,96,123,137,17,208,1,3,164,237,62,64,109,62,71,117,71,184,169,224,169,104,142])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3168#usize 3200#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3168#usize 3200#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [129,168,53,62,31,143,67,207,71,169,96,123,137,17,208,1,3,164,237,62,64,109,62,71,117,71,184,169,224,169,104,142])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3168).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31527).take 32)=(encodeState (JGc_TX2_HashBytes.state [129,168,53,62,31,143,67,207,71,169,96,123,137,17,208,1,3,164,237,62,64,109,62,71,117,71,184,169,224,169,104,142])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3168#usize 3200#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [129,168,53,62,31,143,67,207,71,169,96,123,137,17,208,1,3,164,237,62,64,109,62,71,117,71,184,169,224,169,104,142])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [129,168,53,62,31,143,67,207,71,169,96,123,137,17,208,1,3,164,237,62,64,109,62,71,117,71,184,169,224,169,104,142]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [129,168,53,62,31,143,67,207,71,169,96,123,137,17,208,1,3,164,237,62,64,109,62,71,117,71,184,169,224,169,104,142])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 2880) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
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
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s00 s).«at» 2912#usize)=ok (encodeState (JGc_TX2_HashBytes.state [23,74,195,49,213,135,245,27,57,199,58,222,148,196,183,123,71,5,192,127,140,213,208,209,54,153,86,127,135,105,132,180])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes0 0#usize 0#usize 1#usize 2912#usize 1536#usize
    128#u32 (encodeState value090) (encodeState (JGc_TX2_HashBytes.state [23,74,195,49,213,135,245,27,57,199,58,222,148,196,183,123,71,5,192,127,140,213,208,209,54,153,86,127,135,105,132,180])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read00
  simp only [show 128#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls0.source100 D hash (s00 s) 1#usize 2912#usize 128#u32 0#usize (by decide)
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
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s01 s).«at» 2944#usize)=ok (encodeState (JGc_TX2_HashBytes.state [247,170,236,136,32,227,215,1,30,170,171,104,222,196,102,119,141,43,224,250,73,121,228,110,63,169,195,18,64,55,103,111])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes0 1#usize 1#usize 2#usize 2944#usize 1504#usize
    182#u32 (encodeState value091) (encodeState (JGc_TX2_HashBytes.state [247,170,236,136,32,227,215,1,30,170,171,104,222,196,102,119,141,43,224,250,73,121,228,110,63,169,195,18,64,55,103,111])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read01
  simp only [show 182#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes0 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls0.source101 D hash (s01 s) 2#usize 2944#usize 182#u32 1#usize (by decide)
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
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s02 s).«at» 2976#usize)=ok (encodeState (JGc_TX2_HashBytes.state [190,108,13,171,84,192,94,96,227,48,105,48,244,245,190,168,224,83,16,169,249,226,55,97,180,229,154,227,86,36,50,122])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes0 2#usize 2#usize 3#usize 2976#usize 1472#usize
    288#u32 (encodeState value092) (encodeState (JGc_TX2_HashBytes.state [190,108,13,171,84,192,94,96,227,48,105,48,244,245,190,168,224,83,16,169,249,226,55,97,180,229,154,227,86,36,50,122])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read02
  simp only [show 288#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes0 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls0.source102 D hash (s02 s) 3#usize 2976#usize 288#u32 2#usize (by decide)
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
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s03 s).«at» 3008#usize)=ok (encodeState (JGc_TX2_HashBytes.state [157,66,177,205,179,25,156,253,216,204,238,141,248,146,126,57,146,197,187,130,191,130,41,226,29,137,114,88,159,239,90,188])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes0 3#usize 3#usize 4#usize 3008#usize 1440#usize
    312#u32 (encodeState value093) (encodeState (JGc_TX2_HashBytes.state [157,66,177,205,179,25,156,253,216,204,238,141,248,146,126,57,146,197,187,130,191,130,41,226,29,137,114,88,159,239,90,188])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read03
  simp only [show 312#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes0 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls0.source103 D hash (s03 s) 4#usize 3008#usize 312#u32 3#usize (by decide)
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
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s04 s).«at» 3040#usize)=ok (encodeState (JGc_TX2_HashBytes.state [79,115,19,153,165,205,224,136,61,186,168,120,162,67,201,141,134,174,172,243,21,240,241,100,42,229,53,233,153,170,42,41])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes0 4#usize 4#usize 5#usize 3040#usize 1408#usize
    359#u32 (encodeState value094) (encodeState (JGc_TX2_HashBytes.state [79,115,19,153,165,205,224,136,61,186,168,120,162,67,201,141,134,174,172,243,21,240,241,100,42,229,53,233,153,170,42,41])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read04
  simp only [show 359#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes0 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls0.source104 D hash (s04 s) 5#usize 3040#usize 359#u32 4#usize (by decide)
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
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s05 s).«at» 3072#usize)=ok (encodeState (JGc_TX2_HashBytes.state [148,43,99,22,57,180,71,36,176,106,37,117,42,190,120,213,40,143,126,3,58,186,68,221,194,74,60,125,229,230,106,79])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes0 5#usize 5#usize 6#usize 3072#usize 1376#usize
    375#u32 (encodeState value095) (encodeState (JGc_TX2_HashBytes.state [148,43,99,22,57,180,71,36,176,106,37,117,42,190,120,213,40,143,126,3,58,186,68,221,194,74,60,125,229,230,106,79])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read05
  simp only [show 375#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes0 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls0.source105 D hash (s05 s) 6#usize 3072#usize 375#u32 5#usize (by decide)
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
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s06 s).«at» 3104#usize)=ok (encodeState (JGc_TX2_HashBytes.state [207,102,135,191,134,26,82,182,249,62,205,164,72,118,227,234,90,100,188,183,151,160,216,216,200,245,4,24,126,19,178,5])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes0 6#usize 6#usize 7#usize 3104#usize 1344#usize
    377#u32 (encodeState value096) (encodeState (JGc_TX2_HashBytes.state [207,102,135,191,134,26,82,182,249,62,205,164,72,118,227,234,90,100,188,183,151,160,216,216,200,245,4,24,126,19,178,5])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read06
  simp only [show 377#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes0 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls0.source106 D hash (s06 s) 7#usize 3104#usize 377#u32 6#usize (by decide)
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
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s07 s).«at» 3136#usize)=ok (encodeState (JGc_TX2_HashBytes.state [136,24,60,241,94,194,126,24,120,244,56,48,145,68,42,168,200,103,87,128,189,66,104,116,209,245,141,65,97,81,150,11])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes0 7#usize 7#usize 8#usize 3136#usize 1312#usize
    408#u32 (encodeState value097) (encodeState (JGc_TX2_HashBytes.state [136,24,60,241,94,194,126,24,120,244,56,48,145,68,42,168,200,103,87,128,189,66,104,116,209,245,141,65,97,81,150,11])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read07
  simp only [show 408#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes0 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls0.source107 D hash (s07 s) 8#usize 3136#usize 408#u32 7#usize (by decide)
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
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s08 s).«at» 3168#usize)=ok (encodeState (JGc_TX2_HashBytes.state [236,224,3,7,229,22,125,66,186,131,47,131,187,123,43,166,14,188,255,80,197,222,226,154,83,187,231,109,201,152,99,74])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes0 8#usize 8#usize 9#usize 3168#usize 1280#usize
    423#u32 (encodeState value098) (encodeState (JGc_TX2_HashBytes.state [236,224,3,7,229,22,125,66,186,131,47,131,187,123,43,166,14,188,255,80,197,222,226,154,83,187,231,109,201,152,99,74])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read08
  simp only [show 423#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes0 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls0.source108 D hash (s08 s) 9#usize 3168#usize 423#u32 8#usize (by decide)
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
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s09 s).«at» 3200#usize)=ok (encodeState (JGc_TX2_HashBytes.state [129,168,53,62,31,143,67,207,71,169,96,123,137,17,208,1,3,164,237,62,64,109,62,71,117,71,184,169,224,169,104,142])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes0 9#usize 9#usize 10#usize 3200#usize 1248#usize
    480#u32 (encodeState value099) (encodeState (JGc_TX2_HashBytes.state [129,168,53,62,31,143,67,207,71,169,96,123,137,17,208,1,3,164,237,62,64,109,62,71,117,71,184,169,224,169,104,142])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read09
  simp only [show 480#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes0 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls0.source109 D hash (s09 s) 10#usize 3200#usize 480#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 3200 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 3168 v09
      480#u32 9#usize (encodeState value109) 3200#usize (by decide)
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
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 3200
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level0_09
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level0_10
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHe_C_Gr_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes0
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
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3200#usize 3232#usize)=ok (encodeState (JGc_TX2_HashBytes.state [152,162,255,196,212,132,122,99,218,255,12,162,24,58,6,29,109,82,79,82,141,97,174,54,239,110,201,1,108,154,177,68])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3200#usize 3232#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3200#usize 3232#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [152,162,255,196,212,132,122,99,218,255,12,162,24,58,6,29,109,82,79,82,141,97,174,54,239,110,201,1,108,154,177,68])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3200).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31559).take 32)=(encodeState (JGc_TX2_HashBytes.state [152,162,255,196,212,132,122,99,218,255,12,162,24,58,6,29,109,82,79,82,141,97,174,54,239,110,201,1,108,154,177,68])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3200#usize 3232#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [152,162,255,196,212,132,122,99,218,255,12,162,24,58,6,29,109,82,79,82,141,97,174,54,239,110,201,1,108,154,177,68])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [152,162,255,196,212,132,122,99,218,255,12,162,24,58,6,29,109,82,79,82,141,97,174,54,239,110,201,1,108,154,177,68]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [152,162,255,196,212,132,122,99,218,255,12,162,24,58,6,29,109,82,79,82,141,97,174,54,239,110,201,1,108,154,177,68])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3232#usize 3264#usize)=ok (encodeState (JGc_TX2_HashBytes.state [241,229,149,152,170,27,18,61,206,161,98,30,225,40,233,53,46,62,50,48,254,208,247,99,208,150,81,200,50,240,48,143])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3232#usize 3264#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3232#usize 3264#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [241,229,149,152,170,27,18,61,206,161,98,30,225,40,233,53,46,62,50,48,254,208,247,99,208,150,81,200,50,240,48,143])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3232).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31591).take 32)=(encodeState (JGc_TX2_HashBytes.state [241,229,149,152,170,27,18,61,206,161,98,30,225,40,233,53,46,62,50,48,254,208,247,99,208,150,81,200,50,240,48,143])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3232#usize 3264#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [241,229,149,152,170,27,18,61,206,161,98,30,225,40,233,53,46,62,50,48,254,208,247,99,208,150,81,200,50,240,48,143])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [241,229,149,152,170,27,18,61,206,161,98,30,225,40,233,53,46,62,50,48,254,208,247,99,208,150,81,200,50,240,48,143]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [241,229,149,152,170,27,18,61,206,161,98,30,225,40,233,53,46,62,50,48,254,208,247,99,208,150,81,200,50,240,48,143])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3264#usize 3296#usize)=ok (encodeState (JGc_TX2_HashBytes.state [207,160,0,107,107,203,186,65,189,180,20,58,15,97,7,28,17,81,82,78,101,147,184,188,37,229,216,233,181,44,255,192])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3264#usize 3296#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3264#usize 3296#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [207,160,0,107,107,203,186,65,189,180,20,58,15,97,7,28,17,81,82,78,101,147,184,188,37,229,216,233,181,44,255,192])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3264).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31623).take 32)=(encodeState (JGc_TX2_HashBytes.state [207,160,0,107,107,203,186,65,189,180,20,58,15,97,7,28,17,81,82,78,101,147,184,188,37,229,216,233,181,44,255,192])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3264#usize 3296#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [207,160,0,107,107,203,186,65,189,180,20,58,15,97,7,28,17,81,82,78,101,147,184,188,37,229,216,233,181,44,255,192])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [207,160,0,107,107,203,186,65,189,180,20,58,15,97,7,28,17,81,82,78,101,147,184,188,37,229,216,233,181,44,255,192]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [207,160,0,107,107,203,186,65,189,180,20,58,15,97,7,28,17,81,82,78,101,147,184,188,37,229,216,233,181,44,255,192])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3296#usize 3328#usize)=ok (encodeState (JGc_TX2_HashBytes.state [123,0,162,188,126,191,227,58,109,189,247,38,102,61,157,69,230,4,19,213,18,43,156,113,160,76,253,162,235,123,98,2])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3296#usize 3328#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3296#usize 3328#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [123,0,162,188,126,191,227,58,109,189,247,38,102,61,157,69,230,4,19,213,18,43,156,113,160,76,253,162,235,123,98,2])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3296).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31655).take 32)=(encodeState (JGc_TX2_HashBytes.state [123,0,162,188,126,191,227,58,109,189,247,38,102,61,157,69,230,4,19,213,18,43,156,113,160,76,253,162,235,123,98,2])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3296#usize 3328#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [123,0,162,188,126,191,227,58,109,189,247,38,102,61,157,69,230,4,19,213,18,43,156,113,160,76,253,162,235,123,98,2])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [123,0,162,188,126,191,227,58,109,189,247,38,102,61,157,69,230,4,19,213,18,43,156,113,160,76,253,162,235,123,98,2]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [123,0,162,188,126,191,227,58,109,189,247,38,102,61,157,69,230,4,19,213,18,43,156,113,160,76,253,162,235,123,98,2])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3328#usize 3360#usize)=ok (encodeState (JGc_TX2_HashBytes.state [26,34,190,23,233,18,66,255,141,224,173,247,208,54,188,241,221,59,100,97,57,196,21,248,129,34,192,76,118,155,221,240])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3328#usize 3360#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3328#usize 3360#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [26,34,190,23,233,18,66,255,141,224,173,247,208,54,188,241,221,59,100,97,57,196,21,248,129,34,192,76,118,155,221,240])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3328).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31687).take 32)=(encodeState (JGc_TX2_HashBytes.state [26,34,190,23,233,18,66,255,141,224,173,247,208,54,188,241,221,59,100,97,57,196,21,248,129,34,192,76,118,155,221,240])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3328#usize 3360#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [26,34,190,23,233,18,66,255,141,224,173,247,208,54,188,241,221,59,100,97,57,196,21,248,129,34,192,76,118,155,221,240])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [26,34,190,23,233,18,66,255,141,224,173,247,208,54,188,241,221,59,100,97,57,196,21,248,129,34,192,76,118,155,221,240]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [26,34,190,23,233,18,66,255,141,224,173,247,208,54,188,241,221,59,100,97,57,196,21,248,129,34,192,76,118,155,221,240])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3360#usize 3392#usize)=ok (encodeState (JGc_TX2_HashBytes.state [187,161,232,81,61,204,163,255,108,96,207,42,203,160,95,178,216,58,192,25,156,191,241,239,172,147,29,95,154,104,197,242])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3360#usize 3392#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3360#usize 3392#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [187,161,232,81,61,204,163,255,108,96,207,42,203,160,95,178,216,58,192,25,156,191,241,239,172,147,29,95,154,104,197,242])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3360).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31719).take 32)=(encodeState (JGc_TX2_HashBytes.state [187,161,232,81,61,204,163,255,108,96,207,42,203,160,95,178,216,58,192,25,156,191,241,239,172,147,29,95,154,104,197,242])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3360#usize 3392#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [187,161,232,81,61,204,163,255,108,96,207,42,203,160,95,178,216,58,192,25,156,191,241,239,172,147,29,95,154,104,197,242])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [187,161,232,81,61,204,163,255,108,96,207,42,203,160,95,178,216,58,192,25,156,191,241,239,172,147,29,95,154,104,197,242]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [187,161,232,81,61,204,163,255,108,96,207,42,203,160,95,178,216,58,192,25,156,191,241,239,172,147,29,95,154,104,197,242])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3392#usize 3424#usize)=ok (encodeState (JGc_TX2_HashBytes.state [112,136,211,124,72,204,53,180,236,108,229,56,210,88,160,196,172,44,115,159,237,211,216,230,73,10,77,132,61,136,48,224])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3392#usize 3424#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3392#usize 3424#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [112,136,211,124,72,204,53,180,236,108,229,56,210,88,160,196,172,44,115,159,237,211,216,230,73,10,77,132,61,136,48,224])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3392).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31751).take 32)=(encodeState (JGc_TX2_HashBytes.state [112,136,211,124,72,204,53,180,236,108,229,56,210,88,160,196,172,44,115,159,237,211,216,230,73,10,77,132,61,136,48,224])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3392#usize 3424#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [112,136,211,124,72,204,53,180,236,108,229,56,210,88,160,196,172,44,115,159,237,211,216,230,73,10,77,132,61,136,48,224])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [112,136,211,124,72,204,53,180,236,108,229,56,210,88,160,196,172,44,115,159,237,211,216,230,73,10,77,132,61,136,48,224]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [112,136,211,124,72,204,53,180,236,108,229,56,210,88,160,196,172,44,115,159,237,211,216,230,73,10,77,132,61,136,48,224])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3424#usize 3456#usize)=ok (encodeState (JGc_TX2_HashBytes.state [68,125,166,81,87,6,116,93,85,44,114,64,254,221,200,45,38,25,196,77,234,200,255,231,247,107,222,180,48,23,31,85])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3424#usize 3456#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3424#usize 3456#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [68,125,166,81,87,6,116,93,85,44,114,64,254,221,200,45,38,25,196,77,234,200,255,231,247,107,222,180,48,23,31,85])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3424).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31783).take 32)=(encodeState (JGc_TX2_HashBytes.state [68,125,166,81,87,6,116,93,85,44,114,64,254,221,200,45,38,25,196,77,234,200,255,231,247,107,222,180,48,23,31,85])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3424#usize 3456#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [68,125,166,81,87,6,116,93,85,44,114,64,254,221,200,45,38,25,196,77,234,200,255,231,247,107,222,180,48,23,31,85])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [68,125,166,81,87,6,116,93,85,44,114,64,254,221,200,45,38,25,196,77,234,200,255,231,247,107,222,180,48,23,31,85]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [68,125,166,81,87,6,116,93,85,44,114,64,254,221,200,45,38,25,196,77,234,200,255,231,247,107,222,180,48,23,31,85])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3456#usize 3488#usize)=ok (encodeState (JGc_TX2_HashBytes.state [77,126,21,65,26,159,97,38,195,165,185,168,141,30,194,190,83,101,161,199,214,33,229,162,241,59,159,235,156,208,67,0])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3456#usize 3488#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3456#usize 3488#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [77,126,21,65,26,159,97,38,195,165,185,168,141,30,194,190,83,101,161,199,214,33,229,162,241,59,159,235,156,208,67,0])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3456).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31815).take 32)=(encodeState (JGc_TX2_HashBytes.state [77,126,21,65,26,159,97,38,195,165,185,168,141,30,194,190,83,101,161,199,214,33,229,162,241,59,159,235,156,208,67,0])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3456#usize 3488#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [77,126,21,65,26,159,97,38,195,165,185,168,141,30,194,190,83,101,161,199,214,33,229,162,241,59,159,235,156,208,67,0])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [77,126,21,65,26,159,97,38,195,165,185,168,141,30,194,190,83,101,161,199,214,33,229,162,241,59,159,235,156,208,67,0]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [77,126,21,65,26,159,97,38,195,165,185,168,141,30,194,190,83,101,161,199,214,33,229,162,241,59,159,235,156,208,67,0])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3488#usize 3520#usize)=ok (encodeState (JGc_TX2_HashBytes.state [119,215,118,217,83,7,90,172,138,108,205,252,152,230,120,183,250,105,16,42,20,115,89,179,235,222,70,56,78,50,213,22])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3488#usize 3520#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3488#usize 3520#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [119,215,118,217,83,7,90,172,138,108,205,252,152,230,120,183,250,105,16,42,20,115,89,179,235,222,70,56,78,50,213,22])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3488).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31847).take 32)=(encodeState (JGc_TX2_HashBytes.state [119,215,118,217,83,7,90,172,138,108,205,252,152,230,120,183,250,105,16,42,20,115,89,179,235,222,70,56,78,50,213,22])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3488#usize 3520#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [119,215,118,217,83,7,90,172,138,108,205,252,152,230,120,183,250,105,16,42,20,115,89,179,235,222,70,56,78,50,213,22])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [119,215,118,217,83,7,90,172,138,108,205,252,152,230,120,183,250,105,16,42,20,115,89,179,235,222,70,56,78,50,213,22]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [119,215,118,217,83,7,90,172,138,108,205,252,152,230,120,183,250,105,16,42,20,115,89,179,235,222,70,56,78,50,213,22])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3200) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
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
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s00 s).«at» 3232#usize)=ok (encodeState (JGc_TX2_HashBytes.state [152,162,255,196,212,132,122,99,218,255,12,162,24,58,6,29,109,82,79,82,141,97,174,54,239,110,201,1,108,154,177,68])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes0 0#usize 0#usize 1#usize 3232#usize 1216#usize
    64#u32 (encodeState value100) (encodeState (JGc_TX2_HashBytes.state [152,162,255,196,212,132,122,99,218,255,12,162,24,58,6,29,109,82,79,82,141,97,174,54,239,110,201,1,108,154,177,68])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read00
  simp only [show 64#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls0.source110 D hash (s00 s) 1#usize 3232#usize 64#u32 0#usize (by decide)
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
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s01 s).«at» 3264#usize)=ok (encodeState (JGc_TX2_HashBytes.state [241,229,149,152,170,27,18,61,206,161,98,30,225,40,233,53,46,62,50,48,254,208,247,99,208,150,81,200,50,240,48,143])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes0 1#usize 1#usize 2#usize 3264#usize 1184#usize
    91#u32 (encodeState value101) (encodeState (JGc_TX2_HashBytes.state [241,229,149,152,170,27,18,61,206,161,98,30,225,40,233,53,46,62,50,48,254,208,247,99,208,150,81,200,50,240,48,143])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read01
  simp only [show 91#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes0 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls0.source111 D hash (s01 s) 2#usize 3264#usize 91#u32 1#usize (by decide)
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
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s02 s).«at» 3296#usize)=ok (encodeState (JGc_TX2_HashBytes.state [207,160,0,107,107,203,186,65,189,180,20,58,15,97,7,28,17,81,82,78,101,147,184,188,37,229,216,233,181,44,255,192])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes0 2#usize 2#usize 3#usize 3296#usize 1152#usize
    144#u32 (encodeState value102) (encodeState (JGc_TX2_HashBytes.state [207,160,0,107,107,203,186,65,189,180,20,58,15,97,7,28,17,81,82,78,101,147,184,188,37,229,216,233,181,44,255,192])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read02
  simp only [show 144#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes0 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls0.source112 D hash (s02 s) 3#usize 3296#usize 144#u32 2#usize (by decide)
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
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s03 s).«at» 3328#usize)=ok (encodeState (JGc_TX2_HashBytes.state [123,0,162,188,126,191,227,58,109,189,247,38,102,61,157,69,230,4,19,213,18,43,156,113,160,76,253,162,235,123,98,2])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes0 3#usize 3#usize 4#usize 3328#usize 1120#usize
    156#u32 (encodeState value103) (encodeState (JGc_TX2_HashBytes.state [123,0,162,188,126,191,227,58,109,189,247,38,102,61,157,69,230,4,19,213,18,43,156,113,160,76,253,162,235,123,98,2])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read03
  simp only [show 156#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes0 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls0.source113 D hash (s03 s) 4#usize 3328#usize 156#u32 3#usize (by decide)
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
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s04 s).«at» 3360#usize)=ok (encodeState (JGc_TX2_HashBytes.state [26,34,190,23,233,18,66,255,141,224,173,247,208,54,188,241,221,59,100,97,57,196,21,248,129,34,192,76,118,155,221,240])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes0 4#usize 4#usize 5#usize 3360#usize 1088#usize
    179#u32 (encodeState value104) (encodeState (JGc_TX2_HashBytes.state [26,34,190,23,233,18,66,255,141,224,173,247,208,54,188,241,221,59,100,97,57,196,21,248,129,34,192,76,118,155,221,240])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read04
  simp only [show 179#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes0 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls0.source114 D hash (s04 s) 5#usize 3360#usize 179#u32 4#usize (by decide)
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
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s05 s).«at» 3392#usize)=ok (encodeState (JGc_TX2_HashBytes.state [187,161,232,81,61,204,163,255,108,96,207,42,203,160,95,178,216,58,192,25,156,191,241,239,172,147,29,95,154,104,197,242])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes0 5#usize 5#usize 6#usize 3392#usize 1056#usize
    187#u32 (encodeState value105) (encodeState (JGc_TX2_HashBytes.state [187,161,232,81,61,204,163,255,108,96,207,42,203,160,95,178,216,58,192,25,156,191,241,239,172,147,29,95,154,104,197,242])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read05
  simp only [show 187#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes0 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls0.source115 D hash (s05 s) 6#usize 3392#usize 187#u32 5#usize (by decide)
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
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s06 s).«at» 3424#usize)=ok (encodeState (JGc_TX2_HashBytes.state [112,136,211,124,72,204,53,180,236,108,229,56,210,88,160,196,172,44,115,159,237,211,216,230,73,10,77,132,61,136,48,224])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes0 6#usize 6#usize 7#usize 3424#usize 1024#usize
    188#u32 (encodeState value106) (encodeState (JGc_TX2_HashBytes.state [112,136,211,124,72,204,53,180,236,108,229,56,210,88,160,196,172,44,115,159,237,211,216,230,73,10,77,132,61,136,48,224])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read06
  simp only [show 188#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes0 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls0.source116 D hash (s06 s) 7#usize 3424#usize 188#u32 6#usize (by decide)
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
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s07 s).«at» 3456#usize)=ok (encodeState (JGc_TX2_HashBytes.state [68,125,166,81,87,6,116,93,85,44,114,64,254,221,200,45,38,25,196,77,234,200,255,231,247,107,222,180,48,23,31,85])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes0 7#usize 7#usize 8#usize 3456#usize 992#usize
    204#u32 (encodeState value107) (encodeState (JGc_TX2_HashBytes.state [68,125,166,81,87,6,116,93,85,44,114,64,254,221,200,45,38,25,196,77,234,200,255,231,247,107,222,180,48,23,31,85])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read07
  simp only [show 204#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes0 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls0.source117 D hash (s07 s) 8#usize 3456#usize 204#u32 7#usize (by decide)
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
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s08 s).«at» 3488#usize)=ok (encodeState (JGc_TX2_HashBytes.state [77,126,21,65,26,159,97,38,195,165,185,168,141,30,194,190,83,101,161,199,214,33,229,162,241,59,159,235,156,208,67,0])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes0 8#usize 8#usize 9#usize 3488#usize 960#usize
    211#u32 (encodeState value108) (encodeState (JGc_TX2_HashBytes.state [77,126,21,65,26,159,97,38,195,165,185,168,141,30,194,190,83,101,161,199,214,33,229,162,241,59,159,235,156,208,67,0])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read08
  simp only [show 211#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes0 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls0.source118 D hash (s08 s) 9#usize 3488#usize 211#u32 8#usize (by decide)
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
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s09 s).«at» 3520#usize)=ok (encodeState (JGc_TX2_HashBytes.state [119,215,118,217,83,7,90,172,138,108,205,252,152,230,120,183,250,105,16,42,20,115,89,179,235,222,70,56,78,50,213,22])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes0 9#usize 9#usize 10#usize 3520#usize 928#usize
    240#u32 (encodeState value109) (encodeState (JGc_TX2_HashBytes.state [119,215,118,217,83,7,90,172,138,108,205,252,152,230,120,183,250,105,16,42,20,115,89,179,235,222,70,56,78,50,213,22])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read09
  simp only [show 240#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes0 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls0.source119 D hash (s09 s) 10#usize 3520#usize 240#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 3520 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 3488 v09
      240#u32 9#usize (encodeState value119) 3520#usize (by decide)
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
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 3520
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level0_10
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level0_11
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHe_C_Gr_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes0
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
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3520#usize 3552#usize)=ok (encodeState (JGc_TX2_HashBytes.state [164,65,78,40,106,51,231,38,125,149,75,249,27,93,238,7,155,254,36,78,118,136,30,42,179,250,247,120,7,81,21,144])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3520#usize 3552#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3520#usize 3552#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [164,65,78,40,106,51,231,38,125,149,75,249,27,93,238,7,155,254,36,78,118,136,30,42,179,250,247,120,7,81,21,144])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3520).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31879).take 32)=(encodeState (JGc_TX2_HashBytes.state [164,65,78,40,106,51,231,38,125,149,75,249,27,93,238,7,155,254,36,78,118,136,30,42,179,250,247,120,7,81,21,144])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3520#usize 3552#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [164,65,78,40,106,51,231,38,125,149,75,249,27,93,238,7,155,254,36,78,118,136,30,42,179,250,247,120,7,81,21,144])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [164,65,78,40,106,51,231,38,125,149,75,249,27,93,238,7,155,254,36,78,118,136,30,42,179,250,247,120,7,81,21,144]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [164,65,78,40,106,51,231,38,125,149,75,249,27,93,238,7,155,254,36,78,118,136,30,42,179,250,247,120,7,81,21,144])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3552#usize 3584#usize)=ok (encodeState (JGc_TX2_HashBytes.state [211,245,58,70,112,158,59,164,73,134,77,204,94,119,107,22,183,105,32,45,41,61,170,17,107,25,88,255,149,122,164,95])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3552#usize 3584#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3552#usize 3584#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [211,245,58,70,112,158,59,164,73,134,77,204,94,119,107,22,183,105,32,45,41,61,170,17,107,25,88,255,149,122,164,95])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3552).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31911).take 32)=(encodeState (JGc_TX2_HashBytes.state [211,245,58,70,112,158,59,164,73,134,77,204,94,119,107,22,183,105,32,45,41,61,170,17,107,25,88,255,149,122,164,95])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3552#usize 3584#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [211,245,58,70,112,158,59,164,73,134,77,204,94,119,107,22,183,105,32,45,41,61,170,17,107,25,88,255,149,122,164,95])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [211,245,58,70,112,158,59,164,73,134,77,204,94,119,107,22,183,105,32,45,41,61,170,17,107,25,88,255,149,122,164,95]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [211,245,58,70,112,158,59,164,73,134,77,204,94,119,107,22,183,105,32,45,41,61,170,17,107,25,88,255,149,122,164,95])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3584#usize 3616#usize)=ok (encodeState (JGc_TX2_HashBytes.state [202,64,14,6,35,96,78,97,222,124,133,255,162,222,235,186,63,243,32,144,64,134,253,43,104,226,220,66,124,185,92,7])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3584#usize 3616#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3584#usize 3616#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [202,64,14,6,35,96,78,97,222,124,133,255,162,222,235,186,63,243,32,144,64,134,253,43,104,226,220,66,124,185,92,7])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3584).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31943).take 32)=(encodeState (JGc_TX2_HashBytes.state [202,64,14,6,35,96,78,97,222,124,133,255,162,222,235,186,63,243,32,144,64,134,253,43,104,226,220,66,124,185,92,7])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3584#usize 3616#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [202,64,14,6,35,96,78,97,222,124,133,255,162,222,235,186,63,243,32,144,64,134,253,43,104,226,220,66,124,185,92,7])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [202,64,14,6,35,96,78,97,222,124,133,255,162,222,235,186,63,243,32,144,64,134,253,43,104,226,220,66,124,185,92,7]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [202,64,14,6,35,96,78,97,222,124,133,255,162,222,235,186,63,243,32,144,64,134,253,43,104,226,220,66,124,185,92,7])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3616#usize 3648#usize)=ok (encodeState (JGc_TX2_HashBytes.state [247,131,116,212,93,146,215,2,194,179,95,254,35,17,63,19,206,90,55,80,187,155,124,170,167,224,151,27,162,66,130,234])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3616#usize 3648#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3616#usize 3648#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [247,131,116,212,93,146,215,2,194,179,95,254,35,17,63,19,206,90,55,80,187,155,124,170,167,224,151,27,162,66,130,234])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3616).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 31975).take 32)=(encodeState (JGc_TX2_HashBytes.state [247,131,116,212,93,146,215,2,194,179,95,254,35,17,63,19,206,90,55,80,187,155,124,170,167,224,151,27,162,66,130,234])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3616#usize 3648#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [247,131,116,212,93,146,215,2,194,179,95,254,35,17,63,19,206,90,55,80,187,155,124,170,167,224,151,27,162,66,130,234])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [247,131,116,212,93,146,215,2,194,179,95,254,35,17,63,19,206,90,55,80,187,155,124,170,167,224,151,27,162,66,130,234]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [247,131,116,212,93,146,215,2,194,179,95,254,35,17,63,19,206,90,55,80,187,155,124,170,167,224,151,27,162,66,130,234])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3648#usize 3680#usize)=ok (encodeState (JGc_TX2_HashBytes.state [210,253,93,83,135,24,182,107,129,24,45,138,60,15,178,254,10,77,18,68,97,47,12,113,104,75,135,148,129,15,201,143])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3648#usize 3680#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3648#usize 3680#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [210,253,93,83,135,24,182,107,129,24,45,138,60,15,178,254,10,77,18,68,97,47,12,113,104,75,135,148,129,15,201,143])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3648).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 32007).take 32)=(encodeState (JGc_TX2_HashBytes.state [210,253,93,83,135,24,182,107,129,24,45,138,60,15,178,254,10,77,18,68,97,47,12,113,104,75,135,148,129,15,201,143])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3648#usize 3680#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [210,253,93,83,135,24,182,107,129,24,45,138,60,15,178,254,10,77,18,68,97,47,12,113,104,75,135,148,129,15,201,143])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [210,253,93,83,135,24,182,107,129,24,45,138,60,15,178,254,10,77,18,68,97,47,12,113,104,75,135,148,129,15,201,143]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [210,253,93,83,135,24,182,107,129,24,45,138,60,15,178,254,10,77,18,68,97,47,12,113,104,75,135,148,129,15,201,143])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3680#usize 3712#usize)=ok (encodeState (JGc_TX2_HashBytes.state [108,30,109,110,34,215,172,38,88,37,207,120,123,70,8,40,222,202,101,229,33,117,10,142,69,118,38,35,142,15,136,99])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3680#usize 3712#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3680#usize 3712#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [108,30,109,110,34,215,172,38,88,37,207,120,123,70,8,40,222,202,101,229,33,117,10,142,69,118,38,35,142,15,136,99])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3680).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 32039).take 32)=(encodeState (JGc_TX2_HashBytes.state [108,30,109,110,34,215,172,38,88,37,207,120,123,70,8,40,222,202,101,229,33,117,10,142,69,118,38,35,142,15,136,99])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3680#usize 3712#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [108,30,109,110,34,215,172,38,88,37,207,120,123,70,8,40,222,202,101,229,33,117,10,142,69,118,38,35,142,15,136,99])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [108,30,109,110,34,215,172,38,88,37,207,120,123,70,8,40,222,202,101,229,33,117,10,142,69,118,38,35,142,15,136,99]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [108,30,109,110,34,215,172,38,88,37,207,120,123,70,8,40,222,202,101,229,33,117,10,142,69,118,38,35,142,15,136,99])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3712#usize 3744#usize)=ok (encodeState (JGc_TX2_HashBytes.state [163,133,73,137,234,254,224,77,43,180,89,181,80,182,68,145,168,49,120,172,255,240,170,6,191,185,169,251,210,212,116,243])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3712#usize 3744#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3712#usize 3744#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [163,133,73,137,234,254,224,77,43,180,89,181,80,182,68,145,168,49,120,172,255,240,170,6,191,185,169,251,210,212,116,243])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3712).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 32071).take 32)=(encodeState (JGc_TX2_HashBytes.state [163,133,73,137,234,254,224,77,43,180,89,181,80,182,68,145,168,49,120,172,255,240,170,6,191,185,169,251,210,212,116,243])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3712#usize 3744#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [163,133,73,137,234,254,224,77,43,180,89,181,80,182,68,145,168,49,120,172,255,240,170,6,191,185,169,251,210,212,116,243])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [163,133,73,137,234,254,224,77,43,180,89,181,80,182,68,145,168,49,120,172,255,240,170,6,191,185,169,251,210,212,116,243]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [163,133,73,137,234,254,224,77,43,180,89,181,80,182,68,145,168,49,120,172,255,240,170,6,191,185,169,251,210,212,116,243])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3744#usize 3776#usize)=ok (encodeState (JGc_TX2_HashBytes.state [129,75,194,226,75,93,208,230,67,98,126,175,55,174,113,122,34,52,245,123,168,194,155,56,57,111,31,104,119,113,135,71])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3744#usize 3776#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3744#usize 3776#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [129,75,194,226,75,93,208,230,67,98,126,175,55,174,113,122,34,52,245,123,168,194,155,56,57,111,31,104,119,113,135,71])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3744).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 32103).take 32)=(encodeState (JGc_TX2_HashBytes.state [129,75,194,226,75,93,208,230,67,98,126,175,55,174,113,122,34,52,245,123,168,194,155,56,57,111,31,104,119,113,135,71])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3744#usize 3776#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [129,75,194,226,75,93,208,230,67,98,126,175,55,174,113,122,34,52,245,123,168,194,155,56,57,111,31,104,119,113,135,71])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [129,75,194,226,75,93,208,230,67,98,126,175,55,174,113,122,34,52,245,123,168,194,155,56,57,111,31,104,119,113,135,71]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [129,75,194,226,75,93,208,230,67,98,126,175,55,174,113,122,34,52,245,123,168,194,155,56,57,111,31,104,119,113,135,71])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3776#usize 3808#usize)=ok (encodeState (JGc_TX2_HashBytes.state [56,117,174,192,243,180,43,166,2,52,80,21,16,203,229,105,85,214,216,157,123,230,248,209,219,21,217,60,60,150,184,141])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3776#usize 3808#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3776#usize 3808#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [56,117,174,192,243,180,43,166,2,52,80,21,16,203,229,105,85,214,216,157,123,230,248,209,219,21,217,60,60,150,184,141])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3776).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 32135).take 32)=(encodeState (JGc_TX2_HashBytes.state [56,117,174,192,243,180,43,166,2,52,80,21,16,203,229,105,85,214,216,157,123,230,248,209,219,21,217,60,60,150,184,141])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3776#usize 3808#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [56,117,174,192,243,180,43,166,2,52,80,21,16,203,229,105,85,214,216,157,123,230,248,209,219,21,217,60,60,150,184,141])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [56,117,174,192,243,180,43,166,2,52,80,21,16,203,229,105,85,214,216,157,123,230,248,209,219,21,217,60,60,150,184,141]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [56,117,174,192,243,180,43,166,2,52,80,21,16,203,229,105,85,214,216,157,123,230,248,209,219,21,217,60,60,150,184,141])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      3808#usize 3840#usize)=ok (encodeState (JGc_TX2_HashBytes.state [109,231,155,150,47,42,48,122,18,218,72,65,211,238,180,205,145,47,143,73,158,94,97,67,253,155,2,166,178,50,203,27])) := by
  unfold JGy_G_JGu_Supplied.nodes0
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 3808#usize 3840#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 3808#usize 3840#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [109,231,155,150,47,42,48,122,18,218,72,65,211,238,180,205,145,47,143,73,158,94,97,67,253,155,2,166,178,50,203,27])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 3808).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 32167).take 32)=(encodeState (JGc_TX2_HashBytes.state [109,231,155,150,47,42,48,122,18,218,72,65,211,238,180,205,145,47,143,73,158,94,97,67,253,155,2,166,178,50,203,27])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 3808#usize 3840#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [109,231,155,150,47,42,48,122,18,218,72,65,211,238,180,205,145,47,143,73,158,94,97,67,253,155,2,166,178,50,203,27])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [109,231,155,150,47,42,48,122,18,218,72,65,211,238,180,205,145,47,143,73,158,94,97,67,253,155,2,166,178,50,203,27]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [109,231,155,150,47,42,48,122,18,218,72,65,211,238,180,205,145,47,143,73,158,94,97,67,253,155,2,166,178,50,203,27])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3520) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
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
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s00 s).«at» 3552#usize)=ok (encodeState (JGc_TX2_HashBytes.state [164,65,78,40,106,51,231,38,125,149,75,249,27,93,238,7,155,254,36,78,118,136,30,42,179,250,247,120,7,81,21,144])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes0 0#usize 0#usize 1#usize 3552#usize 896#usize
    32#u32 (encodeState value110) (encodeState (JGc_TX2_HashBytes.state [164,65,78,40,106,51,231,38,125,149,75,249,27,93,238,7,155,254,36,78,118,136,30,42,179,250,247,120,7,81,21,144])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read00
  simp only [show 32#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls0.source120 D hash (s00 s) 1#usize 3552#usize 32#u32 0#usize (by decide)
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
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s01 s).«at» 3584#usize)=ok (encodeState (JGc_TX2_HashBytes.state [211,245,58,70,112,158,59,164,73,134,77,204,94,119,107,22,183,105,32,45,41,61,170,17,107,25,88,255,149,122,164,95])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes0 1#usize 1#usize 2#usize 3584#usize 864#usize
    45#u32 (encodeState value111) (encodeState (JGc_TX2_HashBytes.state [211,245,58,70,112,158,59,164,73,134,77,204,94,119,107,22,183,105,32,45,41,61,170,17,107,25,88,255,149,122,164,95])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read01
  simp only [show 45#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes0 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls0.source121 D hash (s01 s) 2#usize 3584#usize 45#u32 1#usize (by decide)
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
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s02 s).«at» 3616#usize)=ok (encodeState (JGc_TX2_HashBytes.state [202,64,14,6,35,96,78,97,222,124,133,255,162,222,235,186,63,243,32,144,64,134,253,43,104,226,220,66,124,185,92,7])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes0 2#usize 2#usize 3#usize 3616#usize 832#usize
    72#u32 (encodeState value112) (encodeState (JGc_TX2_HashBytes.state [202,64,14,6,35,96,78,97,222,124,133,255,162,222,235,186,63,243,32,144,64,134,253,43,104,226,220,66,124,185,92,7])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read02
  simp only [show 72#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes0 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls0.source122 D hash (s02 s) 3#usize 3616#usize 72#u32 2#usize (by decide)
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
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s03 s).«at» 3648#usize)=ok (encodeState (JGc_TX2_HashBytes.state [247,131,116,212,93,146,215,2,194,179,95,254,35,17,63,19,206,90,55,80,187,155,124,170,167,224,151,27,162,66,130,234])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes0 3#usize 3#usize 4#usize 3648#usize 800#usize
    78#u32 (encodeState value113) (encodeState (JGc_TX2_HashBytes.state [247,131,116,212,93,146,215,2,194,179,95,254,35,17,63,19,206,90,55,80,187,155,124,170,167,224,151,27,162,66,130,234])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read03
  simp only [show 78#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes0 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls0.source123 D hash (s03 s) 4#usize 3648#usize 78#u32 3#usize (by decide)
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
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s04 s).«at» 3680#usize)=ok (encodeState (JGc_TX2_HashBytes.state [210,253,93,83,135,24,182,107,129,24,45,138,60,15,178,254,10,77,18,68,97,47,12,113,104,75,135,148,129,15,201,143])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes0 4#usize 4#usize 5#usize 3680#usize 768#usize
    89#u32 (encodeState value114) (encodeState (JGc_TX2_HashBytes.state [210,253,93,83,135,24,182,107,129,24,45,138,60,15,178,254,10,77,18,68,97,47,12,113,104,75,135,148,129,15,201,143])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read04
  simp only [show 89#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes0 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls0.source124 D hash (s04 s) 5#usize 3680#usize 89#u32 4#usize (by decide)
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
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s05 s).«at» 3712#usize)=ok (encodeState (JGc_TX2_HashBytes.state [108,30,109,110,34,215,172,38,88,37,207,120,123,70,8,40,222,202,101,229,33,117,10,142,69,118,38,35,142,15,136,99])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes0 5#usize 5#usize 6#usize 3712#usize 736#usize
    93#u32 (encodeState value115) (encodeState (JGc_TX2_HashBytes.state [108,30,109,110,34,215,172,38,88,37,207,120,123,70,8,40,222,202,101,229,33,117,10,142,69,118,38,35,142,15,136,99])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read05
  simp only [show 93#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes0 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls0.source125 D hash (s05 s) 6#usize 3712#usize 93#u32 5#usize (by decide)
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
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s06 s).«at» 3744#usize)=ok (encodeState (JGc_TX2_HashBytes.state [163,133,73,137,234,254,224,77,43,180,89,181,80,182,68,145,168,49,120,172,255,240,170,6,191,185,169,251,210,212,116,243])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes0 6#usize 6#usize 7#usize 3744#usize 704#usize
    94#u32 (encodeState value116) (encodeState (JGc_TX2_HashBytes.state [163,133,73,137,234,254,224,77,43,180,89,181,80,182,68,145,168,49,120,172,255,240,170,6,191,185,169,251,210,212,116,243])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read06
  simp only [show 94#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes0 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls0.source126 D hash (s06 s) 7#usize 3744#usize 94#u32 6#usize (by decide)
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
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s07 s).«at» 3776#usize)=ok (encodeState (JGc_TX2_HashBytes.state [129,75,194,226,75,93,208,230,67,98,126,175,55,174,113,122,34,52,245,123,168,194,155,56,57,111,31,104,119,113,135,71])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes0 7#usize 7#usize 8#usize 3776#usize 672#usize
    102#u32 (encodeState value117) (encodeState (JGc_TX2_HashBytes.state [129,75,194,226,75,93,208,230,67,98,126,175,55,174,113,122,34,52,245,123,168,194,155,56,57,111,31,104,119,113,135,71])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read07
  simp only [show 102#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes0 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls0.source127 D hash (s07 s) 8#usize 3776#usize 102#u32 7#usize (by decide)
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
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s08 s).«at» 3808#usize)=ok (encodeState (JGc_TX2_HashBytes.state [56,117,174,192,243,180,43,166,2,52,80,21,16,203,229,105,85,214,216,157,123,230,248,209,219,21,217,60,60,150,184,141])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes0 8#usize 8#usize 9#usize 3808#usize 640#usize
    105#u32 (encodeState value118) (encodeState (JGc_TX2_HashBytes.state [56,117,174,192,243,180,43,166,2,52,80,21,16,203,229,105,85,214,216,157,123,230,248,209,219,21,217,60,60,150,184,141])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read08
  simp only [show 105#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes0 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls0.source128 D hash (s08 s) 9#usize 3808#usize 105#u32 8#usize (by decide)
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
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes0
      (s09 s).«at» 3840#usize)=ok (encodeState (JGc_TX2_HashBytes.state [109,231,155,150,47,42,48,122,18,218,72,65,211,238,180,205,145,47,143,73,158,94,97,67,253,155,2,166,178,50,203,27])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes0 9#usize 9#usize 10#usize 3840#usize 608#usize
    120#u32 (encodeState value119) (encodeState (JGc_TX2_HashBytes.state [109,231,155,150,47,42,48,122,18,218,72,65,211,238,180,205,145,47,143,73,158,94,97,67,253,155,2,166,178,50,203,27])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length0
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length0];decide) read09
  simp only [show 120#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes0 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls0.source129 D hash (s09 s) 10#usize 3840#usize 120#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 3840 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 3808 v09
      120#u32 9#usize (encodeState value129) 3840#usize (by decide)
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
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 3840
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level0_11
end

end
