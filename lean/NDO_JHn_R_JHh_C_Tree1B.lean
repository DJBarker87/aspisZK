import NDO_JHn_R_JHh_C_Tree1B_V0
import RPt_JFq_Range
import NDO_JFw_Frames
import NDO_JGm_TX2_View
import NDO_JGp_Opening0
import NDO_JGp_Opening1
import NDO_JGp_Opening2
import NDO_JGp_Opening3
import NDO_JGp_Opening4
import NDO_JGp_Opening5
import NDO_JGp_Opening6
import NDO_JGp_Opening7
import NDO_JGp_Opening8
import NDO_JGp_Opening9
import NDO_JGu_Keys
import NDO_JGy_LightCore
import NDO_JGy_LightPadding
import NDO_JHn_R_JHh_C_Tree1A
import NDO_JHe_SHARealization
import Port4B_KeyDecode
section
variable [sha : AspisR1.JHe_SHARealization]
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_03
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
def values00 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 8199#u32 0#usize (encodeState value040) 992#usize
 def indices01 : List U32 := [4099#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value040,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 11687#u32 1#usize (encodeState value041) 1024#usize
 def indices02 : List U32 := [4099#u32,5843#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 18441#u32 2#usize (encodeState value042) 1056#usize
 def indices03 : List U32 := [4099#u32,5843#u32,9220#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 19976#u32 3#usize (encodeState value043) 1088#usize
 def indices04 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 22982#u32 4#usize (encodeState value044) 1120#usize
 def indices05 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 24039#u32 5#usize (encodeState value045) 1152#usize
 def indices06 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 24136#u32 6#usize (encodeState value046) 1184#usize
 def indices07 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,26171#u32,27102#u32,30737#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value037,encodeState value038,encodeState value039]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 26171#u32 7#usize (encodeState value047) 1216#usize
 def indices08 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,27102#u32,30737#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value038,encodeState value039]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 27102#u32 8#usize (encodeState value048) 1248#usize
 def indices09 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,30737#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value039]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 30737#u32 9#usize (encodeState value049) 1280#usize
 def indices10 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      960#usize 992#usize)=ok (encodeState (JGc_TX2_HashBytes.state [174,82,153,70,104,229,145,166,155,82,31,251,14,90,80,67,114,199,139,42,46,185,55,221,237,7,39,6,110,203,14,252])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 960#usize 992#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 960#usize 992#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [174,82,153,70,104,229,145,166,155,82,31,251,14,90,80,67,114,199,139,42,46,185,55,221,237,7,39,6,110,203,14,252])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 960).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33991).take 32)=(encodeState (JGc_TX2_HashBytes.state [174,82,153,70,104,229,145,166,155,82,31,251,14,90,80,67,114,199,139,42,46,185,55,221,237,7,39,6,110,203,14,252])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 960#usize 992#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [174,82,153,70,104,229,145,166,155,82,31,251,14,90,80,67,114,199,139,42,46,185,55,221,237,7,39,6,110,203,14,252])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [174,82,153,70,104,229,145,166,155,82,31,251,14,90,80,67,114,199,139,42,46,185,55,221,237,7,39,6,110,203,14,252]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [174,82,153,70,104,229,145,166,155,82,31,251,14,90,80,67,114,199,139,42,46,185,55,221,237,7,39,6,110,203,14,252])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      992#usize 1024#usize)=ok (encodeState (JGc_TX2_HashBytes.state [23,32,94,98,180,20,186,60,5,79,157,234,247,20,120,80,164,35,4,186,25,63,57,161,43,202,149,143,82,86,154,0])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 992#usize 1024#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 992#usize 1024#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [23,32,94,98,180,20,186,60,5,79,157,234,247,20,120,80,164,35,4,186,25,63,57,161,43,202,149,143,82,86,154,0])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 992).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34023).take 32)=(encodeState (JGc_TX2_HashBytes.state [23,32,94,98,180,20,186,60,5,79,157,234,247,20,120,80,164,35,4,186,25,63,57,161,43,202,149,143,82,86,154,0])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 992#usize 1024#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [23,32,94,98,180,20,186,60,5,79,157,234,247,20,120,80,164,35,4,186,25,63,57,161,43,202,149,143,82,86,154,0])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [23,32,94,98,180,20,186,60,5,79,157,234,247,20,120,80,164,35,4,186,25,63,57,161,43,202,149,143,82,86,154,0]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [23,32,94,98,180,20,186,60,5,79,157,234,247,20,120,80,164,35,4,186,25,63,57,161,43,202,149,143,82,86,154,0])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1024#usize 1056#usize)=ok (encodeState (JGc_TX2_HashBytes.state [97,191,57,149,64,167,60,139,155,101,25,14,192,173,197,217,46,87,102,56,173,54,159,44,53,128,93,203,89,224,12,166])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1024#usize 1056#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1024#usize 1056#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [97,191,57,149,64,167,60,139,155,101,25,14,192,173,197,217,46,87,102,56,173,54,159,44,53,128,93,203,89,224,12,166])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1024).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34055).take 32)=(encodeState (JGc_TX2_HashBytes.state [97,191,57,149,64,167,60,139,155,101,25,14,192,173,197,217,46,87,102,56,173,54,159,44,53,128,93,203,89,224,12,166])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1024#usize 1056#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [97,191,57,149,64,167,60,139,155,101,25,14,192,173,197,217,46,87,102,56,173,54,159,44,53,128,93,203,89,224,12,166])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [97,191,57,149,64,167,60,139,155,101,25,14,192,173,197,217,46,87,102,56,173,54,159,44,53,128,93,203,89,224,12,166]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [97,191,57,149,64,167,60,139,155,101,25,14,192,173,197,217,46,87,102,56,173,54,159,44,53,128,93,203,89,224,12,166])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1056#usize 1088#usize)=ok (encodeState (JGc_TX2_HashBytes.state [122,249,177,125,116,181,20,239,10,177,124,212,75,148,64,213,224,76,236,136,246,44,160,184,106,201,206,170,6,68,14,182])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1056#usize 1088#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1056#usize 1088#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [122,249,177,125,116,181,20,239,10,177,124,212,75,148,64,213,224,76,236,136,246,44,160,184,106,201,206,170,6,68,14,182])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1056).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34087).take 32)=(encodeState (JGc_TX2_HashBytes.state [122,249,177,125,116,181,20,239,10,177,124,212,75,148,64,213,224,76,236,136,246,44,160,184,106,201,206,170,6,68,14,182])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1056#usize 1088#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [122,249,177,125,116,181,20,239,10,177,124,212,75,148,64,213,224,76,236,136,246,44,160,184,106,201,206,170,6,68,14,182])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [122,249,177,125,116,181,20,239,10,177,124,212,75,148,64,213,224,76,236,136,246,44,160,184,106,201,206,170,6,68,14,182]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [122,249,177,125,116,181,20,239,10,177,124,212,75,148,64,213,224,76,236,136,246,44,160,184,106,201,206,170,6,68,14,182])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1088#usize 1120#usize)=ok (encodeState (JGc_TX2_HashBytes.state [151,184,78,84,65,195,103,88,59,72,98,75,137,155,138,234,245,102,144,251,199,25,120,222,103,12,202,216,89,102,142,47])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1088#usize 1120#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1088#usize 1120#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [151,184,78,84,65,195,103,88,59,72,98,75,137,155,138,234,245,102,144,251,199,25,120,222,103,12,202,216,89,102,142,47])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1088).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34119).take 32)=(encodeState (JGc_TX2_HashBytes.state [151,184,78,84,65,195,103,88,59,72,98,75,137,155,138,234,245,102,144,251,199,25,120,222,103,12,202,216,89,102,142,47])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1088#usize 1120#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [151,184,78,84,65,195,103,88,59,72,98,75,137,155,138,234,245,102,144,251,199,25,120,222,103,12,202,216,89,102,142,47])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [151,184,78,84,65,195,103,88,59,72,98,75,137,155,138,234,245,102,144,251,199,25,120,222,103,12,202,216,89,102,142,47]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [151,184,78,84,65,195,103,88,59,72,98,75,137,155,138,234,245,102,144,251,199,25,120,222,103,12,202,216,89,102,142,47])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1120#usize 1152#usize)=ok (encodeState (JGc_TX2_HashBytes.state [63,240,224,145,205,168,7,153,218,214,129,218,29,224,241,228,12,94,116,107,157,77,53,249,244,131,19,213,15,234,161,215])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1120#usize 1152#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1120#usize 1152#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [63,240,224,145,205,168,7,153,218,214,129,218,29,224,241,228,12,94,116,107,157,77,53,249,244,131,19,213,15,234,161,215])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1120).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34151).take 32)=(encodeState (JGc_TX2_HashBytes.state [63,240,224,145,205,168,7,153,218,214,129,218,29,224,241,228,12,94,116,107,157,77,53,249,244,131,19,213,15,234,161,215])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1120#usize 1152#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [63,240,224,145,205,168,7,153,218,214,129,218,29,224,241,228,12,94,116,107,157,77,53,249,244,131,19,213,15,234,161,215])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [63,240,224,145,205,168,7,153,218,214,129,218,29,224,241,228,12,94,116,107,157,77,53,249,244,131,19,213,15,234,161,215]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [63,240,224,145,205,168,7,153,218,214,129,218,29,224,241,228,12,94,116,107,157,77,53,249,244,131,19,213,15,234,161,215])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1152#usize 1184#usize)=ok (encodeState (JGc_TX2_HashBytes.state [110,105,159,26,42,122,142,230,234,101,199,61,78,103,131,23,40,10,245,45,225,245,34,241,143,52,113,160,22,153,128,20])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1152#usize 1184#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1152#usize 1184#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [110,105,159,26,42,122,142,230,234,101,199,61,78,103,131,23,40,10,245,45,225,245,34,241,143,52,113,160,22,153,128,20])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1152).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34183).take 32)=(encodeState (JGc_TX2_HashBytes.state [110,105,159,26,42,122,142,230,234,101,199,61,78,103,131,23,40,10,245,45,225,245,34,241,143,52,113,160,22,153,128,20])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1152#usize 1184#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [110,105,159,26,42,122,142,230,234,101,199,61,78,103,131,23,40,10,245,45,225,245,34,241,143,52,113,160,22,153,128,20])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [110,105,159,26,42,122,142,230,234,101,199,61,78,103,131,23,40,10,245,45,225,245,34,241,143,52,113,160,22,153,128,20]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [110,105,159,26,42,122,142,230,234,101,199,61,78,103,131,23,40,10,245,45,225,245,34,241,143,52,113,160,22,153,128,20])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1184#usize 1216#usize)=ok (encodeState (JGc_TX2_HashBytes.state [141,242,62,237,199,13,154,83,181,79,134,159,130,129,160,88,62,217,221,214,111,246,205,241,230,116,152,15,205,136,237,159])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1184#usize 1216#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1184#usize 1216#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [141,242,62,237,199,13,154,83,181,79,134,159,130,129,160,88,62,217,221,214,111,246,205,241,230,116,152,15,205,136,237,159])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1184).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34215).take 32)=(encodeState (JGc_TX2_HashBytes.state [141,242,62,237,199,13,154,83,181,79,134,159,130,129,160,88,62,217,221,214,111,246,205,241,230,116,152,15,205,136,237,159])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1184#usize 1216#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [141,242,62,237,199,13,154,83,181,79,134,159,130,129,160,88,62,217,221,214,111,246,205,241,230,116,152,15,205,136,237,159])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [141,242,62,237,199,13,154,83,181,79,134,159,130,129,160,88,62,217,221,214,111,246,205,241,230,116,152,15,205,136,237,159]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [141,242,62,237,199,13,154,83,181,79,134,159,130,129,160,88,62,217,221,214,111,246,205,241,230,116,152,15,205,136,237,159])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1216#usize 1248#usize)=ok (encodeState (JGc_TX2_HashBytes.state [21,213,50,124,193,142,144,15,46,81,226,121,245,18,87,145,167,20,102,64,173,9,142,30,0,196,36,27,63,68,81,237])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1216#usize 1248#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1216#usize 1248#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [21,213,50,124,193,142,144,15,46,81,226,121,245,18,87,145,167,20,102,64,173,9,142,30,0,196,36,27,63,68,81,237])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1216).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34247).take 32)=(encodeState (JGc_TX2_HashBytes.state [21,213,50,124,193,142,144,15,46,81,226,121,245,18,87,145,167,20,102,64,173,9,142,30,0,196,36,27,63,68,81,237])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1216#usize 1248#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [21,213,50,124,193,142,144,15,46,81,226,121,245,18,87,145,167,20,102,64,173,9,142,30,0,196,36,27,63,68,81,237])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [21,213,50,124,193,142,144,15,46,81,226,121,245,18,87,145,167,20,102,64,173,9,142,30,0,196,36,27,63,68,81,237]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [21,213,50,124,193,142,144,15,46,81,226,121,245,18,87,145,167,20,102,64,173,9,142,30,0,196,36,27,63,68,81,237])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1248#usize 1280#usize)=ok (encodeState (JGc_TX2_HashBytes.state [138,187,147,94,199,192,2,178,20,97,98,68,215,153,0,75,115,196,220,228,200,152,250,238,63,205,135,43,65,81,103,172])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1248#usize 1280#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1248#usize 1280#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [138,187,147,94,199,192,2,178,20,97,98,68,215,153,0,75,115,196,220,228,200,152,250,238,63,205,135,43,65,81,103,172])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1248).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34279).take 32)=(encodeState (JGc_TX2_HashBytes.state [138,187,147,94,199,192,2,178,20,97,98,68,215,153,0,75,115,196,220,228,200,152,250,238,63,205,135,43,65,81,103,172])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1248#usize 1280#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [138,187,147,94,199,192,2,178,20,97,98,68,215,153,0,75,115,196,220,228,200,152,250,238,63,205,135,43,65,81,103,172])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [138,187,147,94,199,192,2,178,20,97,98,68,215,153,0,75,115,196,220,228,200,152,250,238,63,205,135,43,65,81,103,172]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [138,187,147,94,199,192,2,178,20,97,98,68,215,153,0,75,115,196,220,228,200,152,250,238,63,205,135,43,65,81,103,172])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 960) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 1280 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 960 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 8199#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 960 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value030) :=
    JGm_TX2_View.value (s00 s) indices00 values00 960 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=960#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠8199#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨11687#u32,JGm_TX2_View.index (s00 s) indices00 values00 960 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 992#usize)=ok (encodeState (JGc_TX2_HashBytes.state [174,82,153,70,104,229,145,166,155,82,31,251,14,90,80,67,114,199,139,42,46,185,55,221,237,7,39,6,110,203,14,252])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 992#usize 3456#usize
    8199#u32 (encodeState value030) (encodeState (JGc_TX2_HashBytes.state [174,82,153,70,104,229,145,166,155,82,31,251,14,90,80,67,114,199,139,42,46,185,55,221,237,7,39,6,110,203,14,252])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 8199#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source040 D hash (s00 s) 1#usize 992#usize 8199#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 992 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 960 v00
      8199#u32 0#usize (encodeState value040) 992#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 11687#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 992 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value031) :=
    JGm_TX2_View.value (s01 s) indices01 values01 992 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=992#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠11687#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨18441#u32,JGm_TX2_View.index (s01 s) indices01 values01 992 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 1024#usize)=ok (encodeState (JGc_TX2_HashBytes.state [23,32,94,98,180,20,186,60,5,79,157,234,247,20,120,80,164,35,4,186,25,63,57,161,43,202,149,143,82,86,154,0])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 1024#usize 3424#usize
    11687#u32 (encodeState value031) (encodeState (JGc_TX2_HashBytes.state [23,32,94,98,180,20,186,60,5,79,157,234,247,20,120,80,164,35,4,186,25,63,57,161,43,202,149,143,82,86,154,0])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 11687#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source041 D hash (s01 s) 2#usize 1024#usize 11687#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 1024 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 992 v01
      11687#u32 1#usize (encodeState value041) 1024#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 18441#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 1024 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value032) :=
    JGm_TX2_View.value (s02 s) indices02 values02 1024 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=1024#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠18441#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨19976#u32,JGm_TX2_View.index (s02 s) indices02 values02 1024 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s02 s).«at» 1056#usize)=ok (encodeState (JGc_TX2_HashBytes.state [97,191,57,149,64,167,60,139,155,101,25,14,192,173,197,217,46,87,102,56,173,54,159,44,53,128,93,203,89,224,12,166])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 2#usize 3#usize 1056#usize 3392#usize
    18441#u32 (encodeState value032) (encodeState (JGc_TX2_HashBytes.state [97,191,57,149,64,167,60,139,155,101,25,14,192,173,197,217,46,87,102,56,173,54,159,44,53,128,93,203,89,224,12,166])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read02
  simp only [show 18441#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls1.source042 D hash (s02 s) 3#usize 1056#usize 18441#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 1056 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 1024 v02
      18441#u32 2#usize (encodeState value042) 1056#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 19976#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 1056 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value033) :=
    JGm_TX2_View.value (s03 s) indices03 values03 1056 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=1056#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠19976#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨22982#u32,JGm_TX2_View.index (s03 s) indices03 values03 1056 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s03 s).«at» 1088#usize)=ok (encodeState (JGc_TX2_HashBytes.state [122,249,177,125,116,181,20,239,10,177,124,212,75,148,64,213,224,76,236,136,246,44,160,184,106,201,206,170,6,68,14,182])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 3#usize 4#usize 1088#usize 3360#usize
    19976#u32 (encodeState value033) (encodeState (JGc_TX2_HashBytes.state [122,249,177,125,116,181,20,239,10,177,124,212,75,148,64,213,224,76,236,136,246,44,160,184,106,201,206,170,6,68,14,182])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read03
  simp only [show 19976#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls1.source043 D hash (s03 s) 4#usize 1088#usize 19976#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 1088 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 1056 v03
      19976#u32 3#usize (encodeState value043) 1088#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 22982#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 1088 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value034) :=
    JGm_TX2_View.value (s04 s) indices04 values04 1088 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=1088#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠22982#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨24039#u32,JGm_TX2_View.index (s04 s) indices04 values04 1088 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 1120#usize)=ok (encodeState (JGc_TX2_HashBytes.state [151,184,78,84,65,195,103,88,59,72,98,75,137,155,138,234,245,102,144,251,199,25,120,222,103,12,202,216,89,102,142,47])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 4#usize 5#usize 1120#usize 3328#usize
    22982#u32 (encodeState value034) (encodeState (JGc_TX2_HashBytes.state [151,184,78,84,65,195,103,88,59,72,98,75,137,155,138,234,245,102,144,251,199,25,120,222,103,12,202,216,89,102,142,47])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 22982#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source044 D hash (s04 s) 5#usize 1120#usize 22982#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 1120 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 1088 v04
      22982#u32 4#usize (encodeState value044) 1120#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 24039#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 1120 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value035) :=
    JGm_TX2_View.value (s05 s) indices05 values05 1120 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=1120#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠24039#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨24136#u32,JGm_TX2_View.index (s05 s) indices05 values05 1120 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s05 s).«at» 1152#usize)=ok (encodeState (JGc_TX2_HashBytes.state [63,240,224,145,205,168,7,153,218,214,129,218,29,224,241,228,12,94,116,107,157,77,53,249,244,131,19,213,15,234,161,215])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes1 5#usize 5#usize 6#usize 1152#usize 3296#usize
    24039#u32 (encodeState value035) (encodeState (JGc_TX2_HashBytes.state [63,240,224,145,205,168,7,153,218,214,129,218,29,224,241,228,12,94,116,107,157,77,53,249,244,131,19,213,15,234,161,215])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read05
  simp only [show 24039#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls1.source045 D hash (s05 s) 6#usize 1152#usize 24039#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 1152 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 1120 v05
      24039#u32 5#usize (encodeState value045) 1152#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 24136#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 1152 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value036) :=
    JGm_TX2_View.value (s06 s) indices06 values06 1152 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=1152#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠24136#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨26171#u32,JGm_TX2_View.index (s06 s) indices06 values06 1152 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s06 s).«at» 1184#usize)=ok (encodeState (JGc_TX2_HashBytes.state [110,105,159,26,42,122,142,230,234,101,199,61,78,103,131,23,40,10,245,45,225,245,34,241,143,52,113,160,22,153,128,20])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes1 6#usize 6#usize 7#usize 1184#usize 3264#usize
    24136#u32 (encodeState value036) (encodeState (JGc_TX2_HashBytes.state [110,105,159,26,42,122,142,230,234,101,199,61,78,103,131,23,40,10,245,45,225,245,34,241,143,52,113,160,22,153,128,20])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read06
  simp only [show 24136#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls1.source046 D hash (s06 s) 7#usize 1184#usize 24136#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 1184 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 1152 v06
      24136#u32 6#usize (encodeState value046) 1184#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 26171#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 1184 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value037) :=
    JGm_TX2_View.value (s07 s) indices07 values07 1184 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=1184#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠26171#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨27102#u32,JGm_TX2_View.index (s07 s) indices07 values07 1184 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s07 s).«at» 1216#usize)=ok (encodeState (JGc_TX2_HashBytes.state [141,242,62,237,199,13,154,83,181,79,134,159,130,129,160,88,62,217,221,214,111,246,205,241,230,116,152,15,205,136,237,159])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes1 7#usize 7#usize 8#usize 1216#usize 3232#usize
    26171#u32 (encodeState value037) (encodeState (JGc_TX2_HashBytes.state [141,242,62,237,199,13,154,83,181,79,134,159,130,129,160,88,62,217,221,214,111,246,205,241,230,116,152,15,205,136,237,159])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read07
  simp only [show 26171#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls1.source047 D hash (s07 s) 8#usize 1216#usize 26171#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 1216 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 1184 v07
      26171#u32 7#usize (encodeState value047) 1216#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 27102#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 1216 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value038) :=
    JGm_TX2_View.value (s08 s) indices08 values08 1216 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=1216#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠27102#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨30737#u32,JGm_TX2_View.index (s08 s) indices08 values08 1216 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s08 s).«at» 1248#usize)=ok (encodeState (JGc_TX2_HashBytes.state [21,213,50,124,193,142,144,15,46,81,226,121,245,18,87,145,167,20,102,64,173,9,142,30,0,196,36,27,63,68,81,237])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes1 8#usize 8#usize 9#usize 1248#usize 3200#usize
    27102#u32 (encodeState value038) (encodeState (JGc_TX2_HashBytes.state [21,213,50,124,193,142,144,15,46,81,226,121,245,18,87,145,167,20,102,64,173,9,142,30,0,196,36,27,63,68,81,237])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read08
  simp only [show 27102#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls1.source048 D hash (s08 s) 9#usize 1248#usize 27102#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 1248 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 1216 v08
      27102#u32 8#usize (encodeState value048) 1248#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 30737#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 1248 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value039) :=
    JGm_TX2_View.value (s09 s) indices09 values09 1248 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=1248#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠30737#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s09 s).«at» 1280#usize)=ok (encodeState (JGc_TX2_HashBytes.state [138,187,147,94,199,192,2,178,20,97,98,68,215,153,0,75,115,196,220,228,200,152,250,238,63,205,135,43,65,81,103,172])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes1 9#usize 9#usize 10#usize 1280#usize 3168#usize
    30737#u32 (encodeState value039) (encodeState (JGc_TX2_HashBytes.state [138,187,147,94,199,192,2,178,20,97,98,68,215,153,0,75,115,196,220,228,200,152,250,238,63,205,135,43,65,81,103,172])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read09
  simp only [show 30737#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls1.source049 D hash (s09 s) 10#usize 1280#usize 30737#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 1280 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 1248 v09
      30737#u32 9#usize (encodeState value049) 1280#usize (by decide)
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
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 1280
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_03
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_04
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
def values00 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 4099#u32 0#usize (encodeState value050) 1312#usize
 def indices01 : List U32 := [2049#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value050,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 5843#u32 1#usize (encodeState value051) 1344#usize
 def indices02 : List U32 := [2049#u32,2921#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 9220#u32 2#usize (encodeState value052) 1376#usize
 def indices03 : List U32 := [2049#u32,2921#u32,4610#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 9988#u32 3#usize (encodeState value053) 1408#usize
 def indices04 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 11491#u32 4#usize (encodeState value054) 1440#usize
 def indices05 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 12019#u32 5#usize (encodeState value055) 1472#usize
 def indices06 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 12068#u32 6#usize (encodeState value056) 1504#usize
 def indices07 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,13085#u32,13551#u32,15368#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value047,encodeState value048,encodeState value049]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 13085#u32 7#usize (encodeState value057) 1536#usize
 def indices08 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,13551#u32,15368#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value048,encodeState value049]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 13551#u32 8#usize (encodeState value058) 1568#usize
 def indices09 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,15368#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value049]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 15368#u32 9#usize (encodeState value059) 1600#usize
 def indices10 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1280#usize 1312#usize)=ok (encodeState (JGc_TX2_HashBytes.state [213,92,133,128,25,248,250,140,193,139,150,68,77,135,147,35,142,166,119,192,218,182,91,94,228,19,198,108,127,203,242,119])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1280#usize 1312#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1280#usize 1312#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [213,92,133,128,25,248,250,140,193,139,150,68,77,135,147,35,142,166,119,192,218,182,91,94,228,19,198,108,127,203,242,119])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1280).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34311).take 32)=(encodeState (JGc_TX2_HashBytes.state [213,92,133,128,25,248,250,140,193,139,150,68,77,135,147,35,142,166,119,192,218,182,91,94,228,19,198,108,127,203,242,119])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1280#usize 1312#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [213,92,133,128,25,248,250,140,193,139,150,68,77,135,147,35,142,166,119,192,218,182,91,94,228,19,198,108,127,203,242,119])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [213,92,133,128,25,248,250,140,193,139,150,68,77,135,147,35,142,166,119,192,218,182,91,94,228,19,198,108,127,203,242,119]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [213,92,133,128,25,248,250,140,193,139,150,68,77,135,147,35,142,166,119,192,218,182,91,94,228,19,198,108,127,203,242,119])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1312#usize 1344#usize)=ok (encodeState (JGc_TX2_HashBytes.state [81,239,149,218,159,11,224,172,201,3,32,69,184,120,186,14,167,232,10,19,198,22,40,223,87,252,148,18,167,205,157,165])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1312#usize 1344#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1312#usize 1344#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [81,239,149,218,159,11,224,172,201,3,32,69,184,120,186,14,167,232,10,19,198,22,40,223,87,252,148,18,167,205,157,165])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1312).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34343).take 32)=(encodeState (JGc_TX2_HashBytes.state [81,239,149,218,159,11,224,172,201,3,32,69,184,120,186,14,167,232,10,19,198,22,40,223,87,252,148,18,167,205,157,165])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1312#usize 1344#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [81,239,149,218,159,11,224,172,201,3,32,69,184,120,186,14,167,232,10,19,198,22,40,223,87,252,148,18,167,205,157,165])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [81,239,149,218,159,11,224,172,201,3,32,69,184,120,186,14,167,232,10,19,198,22,40,223,87,252,148,18,167,205,157,165]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [81,239,149,218,159,11,224,172,201,3,32,69,184,120,186,14,167,232,10,19,198,22,40,223,87,252,148,18,167,205,157,165])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1344#usize 1376#usize)=ok (encodeState (JGc_TX2_HashBytes.state [218,67,160,176,255,242,51,54,19,70,46,31,66,58,26,18,255,181,5,147,67,43,32,75,58,146,61,9,200,176,17,181])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1344#usize 1376#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1344#usize 1376#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [218,67,160,176,255,242,51,54,19,70,46,31,66,58,26,18,255,181,5,147,67,43,32,75,58,146,61,9,200,176,17,181])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1344).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34375).take 32)=(encodeState (JGc_TX2_HashBytes.state [218,67,160,176,255,242,51,54,19,70,46,31,66,58,26,18,255,181,5,147,67,43,32,75,58,146,61,9,200,176,17,181])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1344#usize 1376#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [218,67,160,176,255,242,51,54,19,70,46,31,66,58,26,18,255,181,5,147,67,43,32,75,58,146,61,9,200,176,17,181])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [218,67,160,176,255,242,51,54,19,70,46,31,66,58,26,18,255,181,5,147,67,43,32,75,58,146,61,9,200,176,17,181]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [218,67,160,176,255,242,51,54,19,70,46,31,66,58,26,18,255,181,5,147,67,43,32,75,58,146,61,9,200,176,17,181])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1376#usize 1408#usize)=ok (encodeState (JGc_TX2_HashBytes.state [9,203,140,76,138,254,212,190,225,220,48,2,142,250,78,110,12,43,32,145,129,4,58,215,255,244,201,225,98,43,227,177])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1376#usize 1408#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1376#usize 1408#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [9,203,140,76,138,254,212,190,225,220,48,2,142,250,78,110,12,43,32,145,129,4,58,215,255,244,201,225,98,43,227,177])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1376).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34407).take 32)=(encodeState (JGc_TX2_HashBytes.state [9,203,140,76,138,254,212,190,225,220,48,2,142,250,78,110,12,43,32,145,129,4,58,215,255,244,201,225,98,43,227,177])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1376#usize 1408#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [9,203,140,76,138,254,212,190,225,220,48,2,142,250,78,110,12,43,32,145,129,4,58,215,255,244,201,225,98,43,227,177])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [9,203,140,76,138,254,212,190,225,220,48,2,142,250,78,110,12,43,32,145,129,4,58,215,255,244,201,225,98,43,227,177]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [9,203,140,76,138,254,212,190,225,220,48,2,142,250,78,110,12,43,32,145,129,4,58,215,255,244,201,225,98,43,227,177])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1408#usize 1440#usize)=ok (encodeState (JGc_TX2_HashBytes.state [248,181,250,118,85,250,26,83,114,52,136,167,60,144,132,111,120,93,125,209,49,84,32,66,30,109,91,89,231,36,237,196])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1408#usize 1440#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1408#usize 1440#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [248,181,250,118,85,250,26,83,114,52,136,167,60,144,132,111,120,93,125,209,49,84,32,66,30,109,91,89,231,36,237,196])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1408).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34439).take 32)=(encodeState (JGc_TX2_HashBytes.state [248,181,250,118,85,250,26,83,114,52,136,167,60,144,132,111,120,93,125,209,49,84,32,66,30,109,91,89,231,36,237,196])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1408#usize 1440#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [248,181,250,118,85,250,26,83,114,52,136,167,60,144,132,111,120,93,125,209,49,84,32,66,30,109,91,89,231,36,237,196])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [248,181,250,118,85,250,26,83,114,52,136,167,60,144,132,111,120,93,125,209,49,84,32,66,30,109,91,89,231,36,237,196]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [248,181,250,118,85,250,26,83,114,52,136,167,60,144,132,111,120,93,125,209,49,84,32,66,30,109,91,89,231,36,237,196])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1440#usize 1472#usize)=ok (encodeState (JGc_TX2_HashBytes.state [108,16,198,203,67,17,242,189,102,34,209,177,45,76,232,181,18,166,239,4,35,21,239,246,220,237,115,171,194,70,204,157])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1440#usize 1472#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1440#usize 1472#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [108,16,198,203,67,17,242,189,102,34,209,177,45,76,232,181,18,166,239,4,35,21,239,246,220,237,115,171,194,70,204,157])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1440).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34471).take 32)=(encodeState (JGc_TX2_HashBytes.state [108,16,198,203,67,17,242,189,102,34,209,177,45,76,232,181,18,166,239,4,35,21,239,246,220,237,115,171,194,70,204,157])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1440#usize 1472#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [108,16,198,203,67,17,242,189,102,34,209,177,45,76,232,181,18,166,239,4,35,21,239,246,220,237,115,171,194,70,204,157])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [108,16,198,203,67,17,242,189,102,34,209,177,45,76,232,181,18,166,239,4,35,21,239,246,220,237,115,171,194,70,204,157]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [108,16,198,203,67,17,242,189,102,34,209,177,45,76,232,181,18,166,239,4,35,21,239,246,220,237,115,171,194,70,204,157])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1472#usize 1504#usize)=ok (encodeState (JGc_TX2_HashBytes.state [197,43,157,201,30,225,68,160,229,190,201,182,162,53,115,97,51,234,182,243,73,166,223,190,116,177,25,188,182,144,219,200])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1472#usize 1504#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1472#usize 1504#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [197,43,157,201,30,225,68,160,229,190,201,182,162,53,115,97,51,234,182,243,73,166,223,190,116,177,25,188,182,144,219,200])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1472).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34503).take 32)=(encodeState (JGc_TX2_HashBytes.state [197,43,157,201,30,225,68,160,229,190,201,182,162,53,115,97,51,234,182,243,73,166,223,190,116,177,25,188,182,144,219,200])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1472#usize 1504#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [197,43,157,201,30,225,68,160,229,190,201,182,162,53,115,97,51,234,182,243,73,166,223,190,116,177,25,188,182,144,219,200])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [197,43,157,201,30,225,68,160,229,190,201,182,162,53,115,97,51,234,182,243,73,166,223,190,116,177,25,188,182,144,219,200]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [197,43,157,201,30,225,68,160,229,190,201,182,162,53,115,97,51,234,182,243,73,166,223,190,116,177,25,188,182,144,219,200])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1504#usize 1536#usize)=ok (encodeState (JGc_TX2_HashBytes.state [48,186,118,148,69,61,104,226,93,243,172,141,168,144,124,254,57,139,1,55,108,253,152,33,72,126,89,125,30,154,10,32])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1504#usize 1536#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1504#usize 1536#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [48,186,118,148,69,61,104,226,93,243,172,141,168,144,124,254,57,139,1,55,108,253,152,33,72,126,89,125,30,154,10,32])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1504).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34535).take 32)=(encodeState (JGc_TX2_HashBytes.state [48,186,118,148,69,61,104,226,93,243,172,141,168,144,124,254,57,139,1,55,108,253,152,33,72,126,89,125,30,154,10,32])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1504#usize 1536#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [48,186,118,148,69,61,104,226,93,243,172,141,168,144,124,254,57,139,1,55,108,253,152,33,72,126,89,125,30,154,10,32])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [48,186,118,148,69,61,104,226,93,243,172,141,168,144,124,254,57,139,1,55,108,253,152,33,72,126,89,125,30,154,10,32]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [48,186,118,148,69,61,104,226,93,243,172,141,168,144,124,254,57,139,1,55,108,253,152,33,72,126,89,125,30,154,10,32])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1536#usize 1568#usize)=ok (encodeState (JGc_TX2_HashBytes.state [90,249,230,45,98,111,180,129,153,122,162,170,204,61,76,254,140,54,104,181,250,67,86,138,44,28,90,64,159,9,181,47])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1536#usize 1568#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1536#usize 1568#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [90,249,230,45,98,111,180,129,153,122,162,170,204,61,76,254,140,54,104,181,250,67,86,138,44,28,90,64,159,9,181,47])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1536).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34567).take 32)=(encodeState (JGc_TX2_HashBytes.state [90,249,230,45,98,111,180,129,153,122,162,170,204,61,76,254,140,54,104,181,250,67,86,138,44,28,90,64,159,9,181,47])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1536#usize 1568#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [90,249,230,45,98,111,180,129,153,122,162,170,204,61,76,254,140,54,104,181,250,67,86,138,44,28,90,64,159,9,181,47])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [90,249,230,45,98,111,180,129,153,122,162,170,204,61,76,254,140,54,104,181,250,67,86,138,44,28,90,64,159,9,181,47]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [90,249,230,45,98,111,180,129,153,122,162,170,204,61,76,254,140,54,104,181,250,67,86,138,44,28,90,64,159,9,181,47])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1568#usize 1600#usize)=ok (encodeState (JGc_TX2_HashBytes.state [195,3,176,84,58,232,36,247,102,253,61,165,20,60,158,89,150,160,29,234,75,87,244,134,24,74,65,119,252,101,75,15])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1568#usize 1600#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1568#usize 1600#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [195,3,176,84,58,232,36,247,102,253,61,165,20,60,158,89,150,160,29,234,75,87,244,134,24,74,65,119,252,101,75,15])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1568).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34599).take 32)=(encodeState (JGc_TX2_HashBytes.state [195,3,176,84,58,232,36,247,102,253,61,165,20,60,158,89,150,160,29,234,75,87,244,134,24,74,65,119,252,101,75,15])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1568#usize 1600#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [195,3,176,84,58,232,36,247,102,253,61,165,20,60,158,89,150,160,29,234,75,87,244,134,24,74,65,119,252,101,75,15])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [195,3,176,84,58,232,36,247,102,253,61,165,20,60,158,89,150,160,29,234,75,87,244,134,24,74,65,119,252,101,75,15]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [195,3,176,84,58,232,36,247,102,253,61,165,20,60,158,89,150,160,29,234,75,87,244,134,24,74,65,119,252,101,75,15])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 1280) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 1600 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 1280 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 4099#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 1280 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value040) :=
    JGm_TX2_View.value (s00 s) indices00 values00 1280 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=1280#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠4099#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨5843#u32,JGm_TX2_View.index (s00 s) indices00 values00 1280 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 1312#usize)=ok (encodeState (JGc_TX2_HashBytes.state [213,92,133,128,25,248,250,140,193,139,150,68,77,135,147,35,142,166,119,192,218,182,91,94,228,19,198,108,127,203,242,119])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 1312#usize 3136#usize
    4099#u32 (encodeState value040) (encodeState (JGc_TX2_HashBytes.state [213,92,133,128,25,248,250,140,193,139,150,68,77,135,147,35,142,166,119,192,218,182,91,94,228,19,198,108,127,203,242,119])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 4099#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source050 D hash (s00 s) 1#usize 1312#usize 4099#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 1312 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 1280 v00
      4099#u32 0#usize (encodeState value050) 1312#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 5843#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 1312 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value041) :=
    JGm_TX2_View.value (s01 s) indices01 values01 1312 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=1312#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠5843#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨9220#u32,JGm_TX2_View.index (s01 s) indices01 values01 1312 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 1344#usize)=ok (encodeState (JGc_TX2_HashBytes.state [81,239,149,218,159,11,224,172,201,3,32,69,184,120,186,14,167,232,10,19,198,22,40,223,87,252,148,18,167,205,157,165])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 1344#usize 3104#usize
    5843#u32 (encodeState value041) (encodeState (JGc_TX2_HashBytes.state [81,239,149,218,159,11,224,172,201,3,32,69,184,120,186,14,167,232,10,19,198,22,40,223,87,252,148,18,167,205,157,165])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 5843#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source051 D hash (s01 s) 2#usize 1344#usize 5843#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 1344 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 1312 v01
      5843#u32 1#usize (encodeState value051) 1344#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 9220#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 1344 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value042) :=
    JGm_TX2_View.value (s02 s) indices02 values02 1344 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=1344#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠9220#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨9988#u32,JGm_TX2_View.index (s02 s) indices02 values02 1344 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s02 s).«at» 1376#usize)=ok (encodeState (JGc_TX2_HashBytes.state [218,67,160,176,255,242,51,54,19,70,46,31,66,58,26,18,255,181,5,147,67,43,32,75,58,146,61,9,200,176,17,181])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 2#usize 3#usize 1376#usize 3072#usize
    9220#u32 (encodeState value042) (encodeState (JGc_TX2_HashBytes.state [218,67,160,176,255,242,51,54,19,70,46,31,66,58,26,18,255,181,5,147,67,43,32,75,58,146,61,9,200,176,17,181])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read02
  simp only [show 9220#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls1.source052 D hash (s02 s) 3#usize 1376#usize 9220#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 1376 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 1344 v02
      9220#u32 2#usize (encodeState value052) 1376#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 9988#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 1376 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value043) :=
    JGm_TX2_View.value (s03 s) indices03 values03 1376 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=1376#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠9988#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨11491#u32,JGm_TX2_View.index (s03 s) indices03 values03 1376 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s03 s).«at» 1408#usize)=ok (encodeState (JGc_TX2_HashBytes.state [9,203,140,76,138,254,212,190,225,220,48,2,142,250,78,110,12,43,32,145,129,4,58,215,255,244,201,225,98,43,227,177])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 3#usize 4#usize 1408#usize 3040#usize
    9988#u32 (encodeState value043) (encodeState (JGc_TX2_HashBytes.state [9,203,140,76,138,254,212,190,225,220,48,2,142,250,78,110,12,43,32,145,129,4,58,215,255,244,201,225,98,43,227,177])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read03
  simp only [show 9988#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls1.source053 D hash (s03 s) 4#usize 1408#usize 9988#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 1408 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 1376 v03
      9988#u32 3#usize (encodeState value053) 1408#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 11491#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 1408 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value044) :=
    JGm_TX2_View.value (s04 s) indices04 values04 1408 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=1408#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠11491#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨12019#u32,JGm_TX2_View.index (s04 s) indices04 values04 1408 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 1440#usize)=ok (encodeState (JGc_TX2_HashBytes.state [248,181,250,118,85,250,26,83,114,52,136,167,60,144,132,111,120,93,125,209,49,84,32,66,30,109,91,89,231,36,237,196])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 4#usize 5#usize 1440#usize 3008#usize
    11491#u32 (encodeState value044) (encodeState (JGc_TX2_HashBytes.state [248,181,250,118,85,250,26,83,114,52,136,167,60,144,132,111,120,93,125,209,49,84,32,66,30,109,91,89,231,36,237,196])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 11491#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source054 D hash (s04 s) 5#usize 1440#usize 11491#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 1440 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 1408 v04
      11491#u32 4#usize (encodeState value054) 1440#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 12019#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 1440 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value045) :=
    JGm_TX2_View.value (s05 s) indices05 values05 1440 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=1440#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠12019#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨12068#u32,JGm_TX2_View.index (s05 s) indices05 values05 1440 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s05 s).«at» 1472#usize)=ok (encodeState (JGc_TX2_HashBytes.state [108,16,198,203,67,17,242,189,102,34,209,177,45,76,232,181,18,166,239,4,35,21,239,246,220,237,115,171,194,70,204,157])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes1 5#usize 5#usize 6#usize 1472#usize 2976#usize
    12019#u32 (encodeState value045) (encodeState (JGc_TX2_HashBytes.state [108,16,198,203,67,17,242,189,102,34,209,177,45,76,232,181,18,166,239,4,35,21,239,246,220,237,115,171,194,70,204,157])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read05
  simp only [show 12019#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls1.source055 D hash (s05 s) 6#usize 1472#usize 12019#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 1472 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 1440 v05
      12019#u32 5#usize (encodeState value055) 1472#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 12068#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 1472 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value046) :=
    JGm_TX2_View.value (s06 s) indices06 values06 1472 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=1472#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠12068#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨13085#u32,JGm_TX2_View.index (s06 s) indices06 values06 1472 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s06 s).«at» 1504#usize)=ok (encodeState (JGc_TX2_HashBytes.state [197,43,157,201,30,225,68,160,229,190,201,182,162,53,115,97,51,234,182,243,73,166,223,190,116,177,25,188,182,144,219,200])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes1 6#usize 6#usize 7#usize 1504#usize 2944#usize
    12068#u32 (encodeState value046) (encodeState (JGc_TX2_HashBytes.state [197,43,157,201,30,225,68,160,229,190,201,182,162,53,115,97,51,234,182,243,73,166,223,190,116,177,25,188,182,144,219,200])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read06
  simp only [show 12068#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls1.source056 D hash (s06 s) 7#usize 1504#usize 12068#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 1504 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 1472 v06
      12068#u32 6#usize (encodeState value056) 1504#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 13085#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 1504 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value047) :=
    JGm_TX2_View.value (s07 s) indices07 values07 1504 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=1504#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠13085#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨13551#u32,JGm_TX2_View.index (s07 s) indices07 values07 1504 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s07 s).«at» 1536#usize)=ok (encodeState (JGc_TX2_HashBytes.state [48,186,118,148,69,61,104,226,93,243,172,141,168,144,124,254,57,139,1,55,108,253,152,33,72,126,89,125,30,154,10,32])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes1 7#usize 7#usize 8#usize 1536#usize 2912#usize
    13085#u32 (encodeState value047) (encodeState (JGc_TX2_HashBytes.state [48,186,118,148,69,61,104,226,93,243,172,141,168,144,124,254,57,139,1,55,108,253,152,33,72,126,89,125,30,154,10,32])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read07
  simp only [show 13085#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls1.source057 D hash (s07 s) 8#usize 1536#usize 13085#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 1536 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 1504 v07
      13085#u32 7#usize (encodeState value057) 1536#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 13551#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 1536 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value048) :=
    JGm_TX2_View.value (s08 s) indices08 values08 1536 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=1536#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠13551#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨15368#u32,JGm_TX2_View.index (s08 s) indices08 values08 1536 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s08 s).«at» 1568#usize)=ok (encodeState (JGc_TX2_HashBytes.state [90,249,230,45,98,111,180,129,153,122,162,170,204,61,76,254,140,54,104,181,250,67,86,138,44,28,90,64,159,9,181,47])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes1 8#usize 8#usize 9#usize 1568#usize 2880#usize
    13551#u32 (encodeState value048) (encodeState (JGc_TX2_HashBytes.state [90,249,230,45,98,111,180,129,153,122,162,170,204,61,76,254,140,54,104,181,250,67,86,138,44,28,90,64,159,9,181,47])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read08
  simp only [show 13551#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls1.source058 D hash (s08 s) 9#usize 1568#usize 13551#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 1568 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 1536 v08
      13551#u32 8#usize (encodeState value058) 1568#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 15368#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 1568 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value049) :=
    JGm_TX2_View.value (s09 s) indices09 values09 1568 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=1568#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠15368#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s09 s).«at» 1600#usize)=ok (encodeState (JGc_TX2_HashBytes.state [195,3,176,84,58,232,36,247,102,253,61,165,20,60,158,89,150,160,29,234,75,87,244,134,24,74,65,119,252,101,75,15])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes1 9#usize 9#usize 10#usize 1600#usize 2848#usize
    15368#u32 (encodeState value049) (encodeState (JGc_TX2_HashBytes.state [195,3,176,84,58,232,36,247,102,253,61,165,20,60,158,89,150,160,29,234,75,87,244,134,24,74,65,119,252,101,75,15])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read09
  simp only [show 15368#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls1.source059 D hash (s09 s) 10#usize 1600#usize 15368#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 1600 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 1568 v09
      15368#u32 9#usize (encodeState value059) 1600#usize (by decide)
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
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 1600
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_04
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_05
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
def values00 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 2049#u32 0#usize (encodeState value060) 1632#usize
 def indices01 : List U32 := [1024#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value060,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 2921#u32 1#usize (encodeState value061) 1664#usize
 def indices02 : List U32 := [1024#u32,1460#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 4610#u32 2#usize (encodeState value062) 1696#usize
 def indices03 : List U32 := [1024#u32,1460#u32,2305#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 4994#u32 3#usize (encodeState value063) 1728#usize
 def indices04 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 5745#u32 4#usize (encodeState value064) 1760#usize
 def indices05 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 6009#u32 5#usize (encodeState value065) 1792#usize
 def indices06 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 6034#u32 6#usize (encodeState value066) 1824#usize
 def indices07 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,6542#u32,6775#u32,7684#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value057,encodeState value058,encodeState value059]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 6542#u32 7#usize (encodeState value067) 1856#usize
 def indices08 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,6775#u32,7684#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value058,encodeState value059]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 6775#u32 8#usize (encodeState value068) 1888#usize
 def indices09 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,7684#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value059]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 7684#u32 9#usize (encodeState value069) 1920#usize
 def indices10 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1600#usize 1632#usize)=ok (encodeState (JGc_TX2_HashBytes.state [184,43,54,143,158,199,175,42,61,237,16,117,244,181,159,43,88,80,126,207,12,253,148,152,128,201,187,77,167,76,234,131])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1600#usize 1632#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1600#usize 1632#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [184,43,54,143,158,199,175,42,61,237,16,117,244,181,159,43,88,80,126,207,12,253,148,152,128,201,187,77,167,76,234,131])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1600).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34631).take 32)=(encodeState (JGc_TX2_HashBytes.state [184,43,54,143,158,199,175,42,61,237,16,117,244,181,159,43,88,80,126,207,12,253,148,152,128,201,187,77,167,76,234,131])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1600#usize 1632#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [184,43,54,143,158,199,175,42,61,237,16,117,244,181,159,43,88,80,126,207,12,253,148,152,128,201,187,77,167,76,234,131])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [184,43,54,143,158,199,175,42,61,237,16,117,244,181,159,43,88,80,126,207,12,253,148,152,128,201,187,77,167,76,234,131]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [184,43,54,143,158,199,175,42,61,237,16,117,244,181,159,43,88,80,126,207,12,253,148,152,128,201,187,77,167,76,234,131])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1632#usize 1664#usize)=ok (encodeState (JGc_TX2_HashBytes.state [9,59,145,89,120,54,222,74,203,219,27,53,98,237,178,181,58,227,170,3,52,21,253,207,237,232,171,52,49,52,153,1])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1632#usize 1664#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1632#usize 1664#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [9,59,145,89,120,54,222,74,203,219,27,53,98,237,178,181,58,227,170,3,52,21,253,207,237,232,171,52,49,52,153,1])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1632).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34663).take 32)=(encodeState (JGc_TX2_HashBytes.state [9,59,145,89,120,54,222,74,203,219,27,53,98,237,178,181,58,227,170,3,52,21,253,207,237,232,171,52,49,52,153,1])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1632#usize 1664#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [9,59,145,89,120,54,222,74,203,219,27,53,98,237,178,181,58,227,170,3,52,21,253,207,237,232,171,52,49,52,153,1])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [9,59,145,89,120,54,222,74,203,219,27,53,98,237,178,181,58,227,170,3,52,21,253,207,237,232,171,52,49,52,153,1]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [9,59,145,89,120,54,222,74,203,219,27,53,98,237,178,181,58,227,170,3,52,21,253,207,237,232,171,52,49,52,153,1])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1664#usize 1696#usize)=ok (encodeState (JGc_TX2_HashBytes.state [200,112,24,187,168,226,133,51,134,133,85,253,45,154,56,190,126,26,87,40,238,99,195,189,69,70,211,132,89,221,161,18])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1664#usize 1696#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1664#usize 1696#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [200,112,24,187,168,226,133,51,134,133,85,253,45,154,56,190,126,26,87,40,238,99,195,189,69,70,211,132,89,221,161,18])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1664).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34695).take 32)=(encodeState (JGc_TX2_HashBytes.state [200,112,24,187,168,226,133,51,134,133,85,253,45,154,56,190,126,26,87,40,238,99,195,189,69,70,211,132,89,221,161,18])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1664#usize 1696#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [200,112,24,187,168,226,133,51,134,133,85,253,45,154,56,190,126,26,87,40,238,99,195,189,69,70,211,132,89,221,161,18])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [200,112,24,187,168,226,133,51,134,133,85,253,45,154,56,190,126,26,87,40,238,99,195,189,69,70,211,132,89,221,161,18]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [200,112,24,187,168,226,133,51,134,133,85,253,45,154,56,190,126,26,87,40,238,99,195,189,69,70,211,132,89,221,161,18])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1696#usize 1728#usize)=ok (encodeState (JGc_TX2_HashBytes.state [254,17,1,69,169,101,14,124,152,58,198,80,91,197,7,201,23,89,197,83,121,49,187,33,254,195,218,154,226,70,10,132])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1696#usize 1728#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1696#usize 1728#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [254,17,1,69,169,101,14,124,152,58,198,80,91,197,7,201,23,89,197,83,121,49,187,33,254,195,218,154,226,70,10,132])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1696).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34727).take 32)=(encodeState (JGc_TX2_HashBytes.state [254,17,1,69,169,101,14,124,152,58,198,80,91,197,7,201,23,89,197,83,121,49,187,33,254,195,218,154,226,70,10,132])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1696#usize 1728#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [254,17,1,69,169,101,14,124,152,58,198,80,91,197,7,201,23,89,197,83,121,49,187,33,254,195,218,154,226,70,10,132])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [254,17,1,69,169,101,14,124,152,58,198,80,91,197,7,201,23,89,197,83,121,49,187,33,254,195,218,154,226,70,10,132]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [254,17,1,69,169,101,14,124,152,58,198,80,91,197,7,201,23,89,197,83,121,49,187,33,254,195,218,154,226,70,10,132])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1728#usize 1760#usize)=ok (encodeState (JGc_TX2_HashBytes.state [192,195,33,171,153,176,59,52,97,96,104,8,183,204,159,49,248,227,95,225,72,109,83,158,159,13,184,26,137,190,18,0])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1728#usize 1760#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1728#usize 1760#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [192,195,33,171,153,176,59,52,97,96,104,8,183,204,159,49,248,227,95,225,72,109,83,158,159,13,184,26,137,190,18,0])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1728).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34759).take 32)=(encodeState (JGc_TX2_HashBytes.state [192,195,33,171,153,176,59,52,97,96,104,8,183,204,159,49,248,227,95,225,72,109,83,158,159,13,184,26,137,190,18,0])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1728#usize 1760#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [192,195,33,171,153,176,59,52,97,96,104,8,183,204,159,49,248,227,95,225,72,109,83,158,159,13,184,26,137,190,18,0])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [192,195,33,171,153,176,59,52,97,96,104,8,183,204,159,49,248,227,95,225,72,109,83,158,159,13,184,26,137,190,18,0]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [192,195,33,171,153,176,59,52,97,96,104,8,183,204,159,49,248,227,95,225,72,109,83,158,159,13,184,26,137,190,18,0])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1760#usize 1792#usize)=ok (encodeState (JGc_TX2_HashBytes.state [254,206,208,23,213,50,19,160,84,122,149,199,15,73,40,119,253,111,116,175,203,205,102,52,143,81,145,192,139,46,139,68])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1760#usize 1792#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1760#usize 1792#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [254,206,208,23,213,50,19,160,84,122,149,199,15,73,40,119,253,111,116,175,203,205,102,52,143,81,145,192,139,46,139,68])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1760).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34791).take 32)=(encodeState (JGc_TX2_HashBytes.state [254,206,208,23,213,50,19,160,84,122,149,199,15,73,40,119,253,111,116,175,203,205,102,52,143,81,145,192,139,46,139,68])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1760#usize 1792#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [254,206,208,23,213,50,19,160,84,122,149,199,15,73,40,119,253,111,116,175,203,205,102,52,143,81,145,192,139,46,139,68])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [254,206,208,23,213,50,19,160,84,122,149,199,15,73,40,119,253,111,116,175,203,205,102,52,143,81,145,192,139,46,139,68]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [254,206,208,23,213,50,19,160,84,122,149,199,15,73,40,119,253,111,116,175,203,205,102,52,143,81,145,192,139,46,139,68])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1792#usize 1824#usize)=ok (encodeState (JGc_TX2_HashBytes.state [135,62,37,121,200,109,211,136,88,24,191,195,231,222,98,12,91,201,86,188,190,61,185,78,66,155,223,88,157,220,23,249])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1792#usize 1824#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1792#usize 1824#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [135,62,37,121,200,109,211,136,88,24,191,195,231,222,98,12,91,201,86,188,190,61,185,78,66,155,223,88,157,220,23,249])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1792).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34823).take 32)=(encodeState (JGc_TX2_HashBytes.state [135,62,37,121,200,109,211,136,88,24,191,195,231,222,98,12,91,201,86,188,190,61,185,78,66,155,223,88,157,220,23,249])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1792#usize 1824#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [135,62,37,121,200,109,211,136,88,24,191,195,231,222,98,12,91,201,86,188,190,61,185,78,66,155,223,88,157,220,23,249])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [135,62,37,121,200,109,211,136,88,24,191,195,231,222,98,12,91,201,86,188,190,61,185,78,66,155,223,88,157,220,23,249]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [135,62,37,121,200,109,211,136,88,24,191,195,231,222,98,12,91,201,86,188,190,61,185,78,66,155,223,88,157,220,23,249])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1824#usize 1856#usize)=ok (encodeState (JGc_TX2_HashBytes.state [195,20,209,28,33,12,185,7,114,250,208,29,236,188,0,141,106,128,113,110,159,175,180,255,243,33,223,145,197,31,0,147])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1824#usize 1856#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1824#usize 1856#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [195,20,209,28,33,12,185,7,114,250,208,29,236,188,0,141,106,128,113,110,159,175,180,255,243,33,223,145,197,31,0,147])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1824).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34855).take 32)=(encodeState (JGc_TX2_HashBytes.state [195,20,209,28,33,12,185,7,114,250,208,29,236,188,0,141,106,128,113,110,159,175,180,255,243,33,223,145,197,31,0,147])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1824#usize 1856#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [195,20,209,28,33,12,185,7,114,250,208,29,236,188,0,141,106,128,113,110,159,175,180,255,243,33,223,145,197,31,0,147])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [195,20,209,28,33,12,185,7,114,250,208,29,236,188,0,141,106,128,113,110,159,175,180,255,243,33,223,145,197,31,0,147]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [195,20,209,28,33,12,185,7,114,250,208,29,236,188,0,141,106,128,113,110,159,175,180,255,243,33,223,145,197,31,0,147])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1856#usize 1888#usize)=ok (encodeState (JGc_TX2_HashBytes.state [98,166,20,210,130,207,194,139,78,117,173,133,188,147,155,169,220,81,13,244,134,242,185,223,105,47,40,3,97,149,255,241])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1856#usize 1888#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1856#usize 1888#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [98,166,20,210,130,207,194,139,78,117,173,133,188,147,155,169,220,81,13,244,134,242,185,223,105,47,40,3,97,149,255,241])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1856).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34887).take 32)=(encodeState (JGc_TX2_HashBytes.state [98,166,20,210,130,207,194,139,78,117,173,133,188,147,155,169,220,81,13,244,134,242,185,223,105,47,40,3,97,149,255,241])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1856#usize 1888#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [98,166,20,210,130,207,194,139,78,117,173,133,188,147,155,169,220,81,13,244,134,242,185,223,105,47,40,3,97,149,255,241])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [98,166,20,210,130,207,194,139,78,117,173,133,188,147,155,169,220,81,13,244,134,242,185,223,105,47,40,3,97,149,255,241]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [98,166,20,210,130,207,194,139,78,117,173,133,188,147,155,169,220,81,13,244,134,242,185,223,105,47,40,3,97,149,255,241])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      1888#usize 1920#usize)=ok (encodeState (JGc_TX2_HashBytes.state [25,110,119,90,229,115,9,14,1,136,89,142,123,146,66,240,29,42,225,45,227,245,237,143,246,109,141,79,34,148,184,86])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 1888#usize 1920#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 1888#usize 1920#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [25,110,119,90,229,115,9,14,1,136,89,142,123,146,66,240,29,42,225,45,227,245,237,143,246,109,141,79,34,148,184,86])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 1888).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 34919).take 32)=(encodeState (JGc_TX2_HashBytes.state [25,110,119,90,229,115,9,14,1,136,89,142,123,146,66,240,29,42,225,45,227,245,237,143,246,109,141,79,34,148,184,86])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 1888#usize 1920#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [25,110,119,90,229,115,9,14,1,136,89,142,123,146,66,240,29,42,225,45,227,245,237,143,246,109,141,79,34,148,184,86])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [25,110,119,90,229,115,9,14,1,136,89,142,123,146,66,240,29,42,225,45,227,245,237,143,246,109,141,79,34,148,184,86]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [25,110,119,90,229,115,9,14,1,136,89,142,123,146,66,240,29,42,225,45,227,245,237,143,246,109,141,79,34,148,184,86])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 1600) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 1920 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 1600 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 2049#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 1600 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value050) :=
    JGm_TX2_View.value (s00 s) indices00 values00 1600 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=1600#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠2049#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2921#u32,JGm_TX2_View.index (s00 s) indices00 values00 1600 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 1632#usize)=ok (encodeState (JGc_TX2_HashBytes.state [184,43,54,143,158,199,175,42,61,237,16,117,244,181,159,43,88,80,126,207,12,253,148,152,128,201,187,77,167,76,234,131])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 1632#usize 2816#usize
    2049#u32 (encodeState value050) (encodeState (JGc_TX2_HashBytes.state [184,43,54,143,158,199,175,42,61,237,16,117,244,181,159,43,88,80,126,207,12,253,148,152,128,201,187,77,167,76,234,131])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 2049#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source060 D hash (s00 s) 1#usize 1632#usize 2049#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 1632 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 1600 v00
      2049#u32 0#usize (encodeState value060) 1632#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 2921#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 1632 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value051) :=
    JGm_TX2_View.value (s01 s) indices01 values01 1632 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=1632#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠2921#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨4610#u32,JGm_TX2_View.index (s01 s) indices01 values01 1632 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 1664#usize)=ok (encodeState (JGc_TX2_HashBytes.state [9,59,145,89,120,54,222,74,203,219,27,53,98,237,178,181,58,227,170,3,52,21,253,207,237,232,171,52,49,52,153,1])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 1664#usize 2784#usize
    2921#u32 (encodeState value051) (encodeState (JGc_TX2_HashBytes.state [9,59,145,89,120,54,222,74,203,219,27,53,98,237,178,181,58,227,170,3,52,21,253,207,237,232,171,52,49,52,153,1])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 2921#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source061 D hash (s01 s) 2#usize 1664#usize 2921#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 1664 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 1632 v01
      2921#u32 1#usize (encodeState value061) 1664#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 4610#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 1664 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value052) :=
    JGm_TX2_View.value (s02 s) indices02 values02 1664 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=1664#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠4610#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨4994#u32,JGm_TX2_View.index (s02 s) indices02 values02 1664 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s02 s).«at» 1696#usize)=ok (encodeState (JGc_TX2_HashBytes.state [200,112,24,187,168,226,133,51,134,133,85,253,45,154,56,190,126,26,87,40,238,99,195,189,69,70,211,132,89,221,161,18])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 2#usize 3#usize 1696#usize 2752#usize
    4610#u32 (encodeState value052) (encodeState (JGc_TX2_HashBytes.state [200,112,24,187,168,226,133,51,134,133,85,253,45,154,56,190,126,26,87,40,238,99,195,189,69,70,211,132,89,221,161,18])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read02
  simp only [show 4610#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls1.source062 D hash (s02 s) 3#usize 1696#usize 4610#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 1696 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 1664 v02
      4610#u32 2#usize (encodeState value062) 1696#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 4994#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 1696 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value053) :=
    JGm_TX2_View.value (s03 s) indices03 values03 1696 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=1696#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠4994#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨5745#u32,JGm_TX2_View.index (s03 s) indices03 values03 1696 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s03 s).«at» 1728#usize)=ok (encodeState (JGc_TX2_HashBytes.state [254,17,1,69,169,101,14,124,152,58,198,80,91,197,7,201,23,89,197,83,121,49,187,33,254,195,218,154,226,70,10,132])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 3#usize 4#usize 1728#usize 2720#usize
    4994#u32 (encodeState value053) (encodeState (JGc_TX2_HashBytes.state [254,17,1,69,169,101,14,124,152,58,198,80,91,197,7,201,23,89,197,83,121,49,187,33,254,195,218,154,226,70,10,132])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read03
  simp only [show 4994#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls1.source063 D hash (s03 s) 4#usize 1728#usize 4994#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 1728 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 1696 v03
      4994#u32 3#usize (encodeState value063) 1728#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 5745#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 1728 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value054) :=
    JGm_TX2_View.value (s04 s) indices04 values04 1728 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=1728#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠5745#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨6009#u32,JGm_TX2_View.index (s04 s) indices04 values04 1728 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 1760#usize)=ok (encodeState (JGc_TX2_HashBytes.state [192,195,33,171,153,176,59,52,97,96,104,8,183,204,159,49,248,227,95,225,72,109,83,158,159,13,184,26,137,190,18,0])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 4#usize 5#usize 1760#usize 2688#usize
    5745#u32 (encodeState value054) (encodeState (JGc_TX2_HashBytes.state [192,195,33,171,153,176,59,52,97,96,104,8,183,204,159,49,248,227,95,225,72,109,83,158,159,13,184,26,137,190,18,0])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 5745#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source064 D hash (s04 s) 5#usize 1760#usize 5745#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 1760 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 1728 v04
      5745#u32 4#usize (encodeState value064) 1760#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 6009#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 1760 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value055) :=
    JGm_TX2_View.value (s05 s) indices05 values05 1760 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=1760#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠6009#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨6034#u32,JGm_TX2_View.index (s05 s) indices05 values05 1760 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s05 s).«at» 1792#usize)=ok (encodeState (JGc_TX2_HashBytes.state [254,206,208,23,213,50,19,160,84,122,149,199,15,73,40,119,253,111,116,175,203,205,102,52,143,81,145,192,139,46,139,68])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes1 5#usize 5#usize 6#usize 1792#usize 2656#usize
    6009#u32 (encodeState value055) (encodeState (JGc_TX2_HashBytes.state [254,206,208,23,213,50,19,160,84,122,149,199,15,73,40,119,253,111,116,175,203,205,102,52,143,81,145,192,139,46,139,68])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read05
  simp only [show 6009#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls1.source065 D hash (s05 s) 6#usize 1792#usize 6009#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 1792 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 1760 v05
      6009#u32 5#usize (encodeState value065) 1792#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 6034#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 1792 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value056) :=
    JGm_TX2_View.value (s06 s) indices06 values06 1792 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=1792#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠6034#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨6542#u32,JGm_TX2_View.index (s06 s) indices06 values06 1792 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s06 s).«at» 1824#usize)=ok (encodeState (JGc_TX2_HashBytes.state [135,62,37,121,200,109,211,136,88,24,191,195,231,222,98,12,91,201,86,188,190,61,185,78,66,155,223,88,157,220,23,249])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes1 6#usize 6#usize 7#usize 1824#usize 2624#usize
    6034#u32 (encodeState value056) (encodeState (JGc_TX2_HashBytes.state [135,62,37,121,200,109,211,136,88,24,191,195,231,222,98,12,91,201,86,188,190,61,185,78,66,155,223,88,157,220,23,249])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read06
  simp only [show 6034#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls1.source066 D hash (s06 s) 7#usize 1824#usize 6034#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 1824 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 1792 v06
      6034#u32 6#usize (encodeState value066) 1824#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 6542#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 1824 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value057) :=
    JGm_TX2_View.value (s07 s) indices07 values07 1824 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=1824#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠6542#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨6775#u32,JGm_TX2_View.index (s07 s) indices07 values07 1824 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s07 s).«at» 1856#usize)=ok (encodeState (JGc_TX2_HashBytes.state [195,20,209,28,33,12,185,7,114,250,208,29,236,188,0,141,106,128,113,110,159,175,180,255,243,33,223,145,197,31,0,147])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes1 7#usize 7#usize 8#usize 1856#usize 2592#usize
    6542#u32 (encodeState value057) (encodeState (JGc_TX2_HashBytes.state [195,20,209,28,33,12,185,7,114,250,208,29,236,188,0,141,106,128,113,110,159,175,180,255,243,33,223,145,197,31,0,147])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read07
  simp only [show 6542#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls1.source067 D hash (s07 s) 8#usize 1856#usize 6542#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 1856 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 1824 v07
      6542#u32 7#usize (encodeState value067) 1856#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 6775#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 1856 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value058) :=
    JGm_TX2_View.value (s08 s) indices08 values08 1856 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=1856#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠6775#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨7684#u32,JGm_TX2_View.index (s08 s) indices08 values08 1856 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s08 s).«at» 1888#usize)=ok (encodeState (JGc_TX2_HashBytes.state [98,166,20,210,130,207,194,139,78,117,173,133,188,147,155,169,220,81,13,244,134,242,185,223,105,47,40,3,97,149,255,241])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes1 8#usize 8#usize 9#usize 1888#usize 2560#usize
    6775#u32 (encodeState value058) (encodeState (JGc_TX2_HashBytes.state [98,166,20,210,130,207,194,139,78,117,173,133,188,147,155,169,220,81,13,244,134,242,185,223,105,47,40,3,97,149,255,241])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read08
  simp only [show 6775#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls1.source068 D hash (s08 s) 9#usize 1888#usize 6775#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 1888 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 1856 v08
      6775#u32 8#usize (encodeState value068) 1888#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 7684#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 1888 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value059) :=
    JGm_TX2_View.value (s09 s) indices09 values09 1888 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=1888#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠7684#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s09 s).«at» 1920#usize)=ok (encodeState (JGc_TX2_HashBytes.state [25,110,119,90,229,115,9,14,1,136,89,142,123,146,66,240,29,42,225,45,227,245,237,143,246,109,141,79,34,148,184,86])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes1 9#usize 9#usize 10#usize 1920#usize 2528#usize
    7684#u32 (encodeState value059) (encodeState (JGc_TX2_HashBytes.state [25,110,119,90,229,115,9,14,1,136,89,142,123,146,66,240,29,42,225,45,227,245,237,143,246,109,141,79,34,148,184,86])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read09
  simp only [show 7684#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls1.source069 D hash (s09 s) 10#usize 1920#usize 7684#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 1920 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 1888 v09
      7684#u32 9#usize (encodeState value069) 1920#usize (by decide)
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
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 1920
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_05
end

end
