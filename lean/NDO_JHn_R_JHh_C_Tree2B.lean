import NDO_JHn_R_JHh_C_Tree2B_V0
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
import NDO_JHn_R_JHh_C_Tree2A
import NDO_JHe_SHARealization
import Port4B_KeyDecode
section
variable [sha : AspisR1.JHe_SHARealization]
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level2_03
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes2
def indices00 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
def values00 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 2049#u32 0#usize (encodeState value040) 992#usize
 def indices01 : List U32 := [1024#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value040,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 2921#u32 1#usize (encodeState value041) 1024#usize
 def indices02 : List U32 := [1024#u32,1460#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 4610#u32 2#usize (encodeState value042) 1056#usize
 def indices03 : List U32 := [1024#u32,1460#u32,2305#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 4994#u32 3#usize (encodeState value043) 1088#usize
 def indices04 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 5745#u32 4#usize (encodeState value044) 1120#usize
 def indices05 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 6009#u32 5#usize (encodeState value045) 1152#usize
 def indices06 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 6034#u32 6#usize (encodeState value046) 1184#usize
 def indices07 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,6542#u32,6775#u32,7684#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value037,encodeState value038,encodeState value039]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 6542#u32 7#usize (encodeState value047) 1216#usize
 def indices08 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,6775#u32,7684#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value038,encodeState value039]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 6775#u32 8#usize (encodeState value048) 1248#usize
 def indices09 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,7684#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value039]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 7684#u32 9#usize (encodeState value049) 1280#usize
 def indices10 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      960#usize 992#usize)=ok (encodeState (JGc_TX2_HashBytes.state [249,97,95,72,195,239,230,133,231,204,195,159,197,242,53,210,181,126,161,238,155,106,151,110,88,108,146,232,8,121,248,62])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 960#usize 992#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 960#usize 992#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [249,97,95,72,195,239,230,133,231,204,195,159,197,242,53,210,181,126,161,238,155,106,151,110,88,108,146,232,8,121,248,62])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 960).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38663).take 32)=(encodeState (JGc_TX2_HashBytes.state [249,97,95,72,195,239,230,133,231,204,195,159,197,242,53,210,181,126,161,238,155,106,151,110,88,108,146,232,8,121,248,62])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 960#usize 992#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [249,97,95,72,195,239,230,133,231,204,195,159,197,242,53,210,181,126,161,238,155,106,151,110,88,108,146,232,8,121,248,62])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [249,97,95,72,195,239,230,133,231,204,195,159,197,242,53,210,181,126,161,238,155,106,151,110,88,108,146,232,8,121,248,62]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [249,97,95,72,195,239,230,133,231,204,195,159,197,242,53,210,181,126,161,238,155,106,151,110,88,108,146,232,8,121,248,62])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      992#usize 1024#usize)=ok (encodeState (JGc_TX2_HashBytes.state [179,62,84,67,145,245,19,145,0,76,183,216,254,164,78,100,235,197,149,22,181,176,111,192,90,35,170,224,190,165,169,130])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 992#usize 1024#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 992#usize 1024#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [179,62,84,67,145,245,19,145,0,76,183,216,254,164,78,100,235,197,149,22,181,176,111,192,90,35,170,224,190,165,169,130])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 992).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38695).take 32)=(encodeState (JGc_TX2_HashBytes.state [179,62,84,67,145,245,19,145,0,76,183,216,254,164,78,100,235,197,149,22,181,176,111,192,90,35,170,224,190,165,169,130])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 992#usize 1024#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [179,62,84,67,145,245,19,145,0,76,183,216,254,164,78,100,235,197,149,22,181,176,111,192,90,35,170,224,190,165,169,130])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [179,62,84,67,145,245,19,145,0,76,183,216,254,164,78,100,235,197,149,22,181,176,111,192,90,35,170,224,190,165,169,130]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [179,62,84,67,145,245,19,145,0,76,183,216,254,164,78,100,235,197,149,22,181,176,111,192,90,35,170,224,190,165,169,130])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1024#usize 1056#usize)=ok (encodeState (JGc_TX2_HashBytes.state [169,21,194,86,169,83,68,57,145,59,224,82,4,255,183,95,137,88,198,233,243,230,177,89,132,186,175,162,5,209,79,171])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1024#usize 1056#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1024#usize 1056#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [169,21,194,86,169,83,68,57,145,59,224,82,4,255,183,95,137,88,198,233,243,230,177,89,132,186,175,162,5,209,79,171])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1024).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38727).take 32)=(encodeState (JGc_TX2_HashBytes.state [169,21,194,86,169,83,68,57,145,59,224,82,4,255,183,95,137,88,198,233,243,230,177,89,132,186,175,162,5,209,79,171])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1024#usize 1056#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [169,21,194,86,169,83,68,57,145,59,224,82,4,255,183,95,137,88,198,233,243,230,177,89,132,186,175,162,5,209,79,171])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [169,21,194,86,169,83,68,57,145,59,224,82,4,255,183,95,137,88,198,233,243,230,177,89,132,186,175,162,5,209,79,171]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [169,21,194,86,169,83,68,57,145,59,224,82,4,255,183,95,137,88,198,233,243,230,177,89,132,186,175,162,5,209,79,171])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1056#usize 1088#usize)=ok (encodeState (JGc_TX2_HashBytes.state [249,125,104,173,124,225,131,121,245,201,10,19,165,30,103,92,67,162,190,80,0,142,172,114,183,72,182,186,237,7,60,125])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1056#usize 1088#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1056#usize 1088#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [249,125,104,173,124,225,131,121,245,201,10,19,165,30,103,92,67,162,190,80,0,142,172,114,183,72,182,186,237,7,60,125])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1056).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38759).take 32)=(encodeState (JGc_TX2_HashBytes.state [249,125,104,173,124,225,131,121,245,201,10,19,165,30,103,92,67,162,190,80,0,142,172,114,183,72,182,186,237,7,60,125])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1056#usize 1088#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [249,125,104,173,124,225,131,121,245,201,10,19,165,30,103,92,67,162,190,80,0,142,172,114,183,72,182,186,237,7,60,125])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [249,125,104,173,124,225,131,121,245,201,10,19,165,30,103,92,67,162,190,80,0,142,172,114,183,72,182,186,237,7,60,125]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [249,125,104,173,124,225,131,121,245,201,10,19,165,30,103,92,67,162,190,80,0,142,172,114,183,72,182,186,237,7,60,125])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1088#usize 1120#usize)=ok (encodeState (JGc_TX2_HashBytes.state [195,11,91,13,242,157,237,14,230,48,53,152,68,28,146,173,39,23,72,54,22,225,121,215,107,229,54,60,170,68,238,72])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1088#usize 1120#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1088#usize 1120#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [195,11,91,13,242,157,237,14,230,48,53,152,68,28,146,173,39,23,72,54,22,225,121,215,107,229,54,60,170,68,238,72])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1088).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38791).take 32)=(encodeState (JGc_TX2_HashBytes.state [195,11,91,13,242,157,237,14,230,48,53,152,68,28,146,173,39,23,72,54,22,225,121,215,107,229,54,60,170,68,238,72])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1088#usize 1120#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [195,11,91,13,242,157,237,14,230,48,53,152,68,28,146,173,39,23,72,54,22,225,121,215,107,229,54,60,170,68,238,72])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [195,11,91,13,242,157,237,14,230,48,53,152,68,28,146,173,39,23,72,54,22,225,121,215,107,229,54,60,170,68,238,72]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [195,11,91,13,242,157,237,14,230,48,53,152,68,28,146,173,39,23,72,54,22,225,121,215,107,229,54,60,170,68,238,72])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1120#usize 1152#usize)=ok (encodeState (JGc_TX2_HashBytes.state [179,112,196,108,44,160,62,125,194,38,29,185,108,215,4,140,11,246,68,159,82,31,45,80,100,31,239,92,243,120,250,219])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1120#usize 1152#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1120#usize 1152#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [179,112,196,108,44,160,62,125,194,38,29,185,108,215,4,140,11,246,68,159,82,31,45,80,100,31,239,92,243,120,250,219])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1120).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38823).take 32)=(encodeState (JGc_TX2_HashBytes.state [179,112,196,108,44,160,62,125,194,38,29,185,108,215,4,140,11,246,68,159,82,31,45,80,100,31,239,92,243,120,250,219])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1120#usize 1152#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [179,112,196,108,44,160,62,125,194,38,29,185,108,215,4,140,11,246,68,159,82,31,45,80,100,31,239,92,243,120,250,219])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [179,112,196,108,44,160,62,125,194,38,29,185,108,215,4,140,11,246,68,159,82,31,45,80,100,31,239,92,243,120,250,219]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [179,112,196,108,44,160,62,125,194,38,29,185,108,215,4,140,11,246,68,159,82,31,45,80,100,31,239,92,243,120,250,219])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1152#usize 1184#usize)=ok (encodeState (JGc_TX2_HashBytes.state [62,167,250,165,65,31,182,78,176,251,194,75,161,83,115,3,81,118,25,197,64,0,255,47,232,78,185,56,42,93,69,86])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1152#usize 1184#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1152#usize 1184#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [62,167,250,165,65,31,182,78,176,251,194,75,161,83,115,3,81,118,25,197,64,0,255,47,232,78,185,56,42,93,69,86])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1152).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38855).take 32)=(encodeState (JGc_TX2_HashBytes.state [62,167,250,165,65,31,182,78,176,251,194,75,161,83,115,3,81,118,25,197,64,0,255,47,232,78,185,56,42,93,69,86])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1152#usize 1184#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [62,167,250,165,65,31,182,78,176,251,194,75,161,83,115,3,81,118,25,197,64,0,255,47,232,78,185,56,42,93,69,86])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [62,167,250,165,65,31,182,78,176,251,194,75,161,83,115,3,81,118,25,197,64,0,255,47,232,78,185,56,42,93,69,86]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [62,167,250,165,65,31,182,78,176,251,194,75,161,83,115,3,81,118,25,197,64,0,255,47,232,78,185,56,42,93,69,86])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1184#usize 1216#usize)=ok (encodeState (JGc_TX2_HashBytes.state [57,54,77,49,101,42,95,108,7,193,128,156,160,108,172,205,176,94,234,119,178,60,14,61,107,83,83,99,46,128,55,36])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1184#usize 1216#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1184#usize 1216#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [57,54,77,49,101,42,95,108,7,193,128,156,160,108,172,205,176,94,234,119,178,60,14,61,107,83,83,99,46,128,55,36])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1184).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38887).take 32)=(encodeState (JGc_TX2_HashBytes.state [57,54,77,49,101,42,95,108,7,193,128,156,160,108,172,205,176,94,234,119,178,60,14,61,107,83,83,99,46,128,55,36])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1184#usize 1216#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [57,54,77,49,101,42,95,108,7,193,128,156,160,108,172,205,176,94,234,119,178,60,14,61,107,83,83,99,46,128,55,36])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [57,54,77,49,101,42,95,108,7,193,128,156,160,108,172,205,176,94,234,119,178,60,14,61,107,83,83,99,46,128,55,36]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [57,54,77,49,101,42,95,108,7,193,128,156,160,108,172,205,176,94,234,119,178,60,14,61,107,83,83,99,46,128,55,36])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1216#usize 1248#usize)=ok (encodeState (JGc_TX2_HashBytes.state [162,78,44,26,160,83,123,134,218,232,6,213,29,159,101,194,116,107,147,229,122,88,91,82,166,42,5,120,181,179,197,167])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1216#usize 1248#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1216#usize 1248#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [162,78,44,26,160,83,123,134,218,232,6,213,29,159,101,194,116,107,147,229,122,88,91,82,166,42,5,120,181,179,197,167])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1216).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38919).take 32)=(encodeState (JGc_TX2_HashBytes.state [162,78,44,26,160,83,123,134,218,232,6,213,29,159,101,194,116,107,147,229,122,88,91,82,166,42,5,120,181,179,197,167])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1216#usize 1248#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [162,78,44,26,160,83,123,134,218,232,6,213,29,159,101,194,116,107,147,229,122,88,91,82,166,42,5,120,181,179,197,167])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [162,78,44,26,160,83,123,134,218,232,6,213,29,159,101,194,116,107,147,229,122,88,91,82,166,42,5,120,181,179,197,167]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [162,78,44,26,160,83,123,134,218,232,6,213,29,159,101,194,116,107,147,229,122,88,91,82,166,42,5,120,181,179,197,167])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1248#usize 1280#usize)=ok (encodeState (JGc_TX2_HashBytes.state [16,233,214,196,219,235,118,177,214,211,77,23,126,52,140,234,128,247,206,133,105,180,135,29,2,2,189,128,41,90,9,193])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1248#usize 1280#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1248#usize 1280#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [16,233,214,196,219,235,118,177,214,211,77,23,126,52,140,234,128,247,206,133,105,180,135,29,2,2,189,128,41,90,9,193])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1248).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38951).take 32)=(encodeState (JGc_TX2_HashBytes.state [16,233,214,196,219,235,118,177,214,211,77,23,126,52,140,234,128,247,206,133,105,180,135,29,2,2,189,128,41,90,9,193])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1248#usize 1280#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [16,233,214,196,219,235,118,177,214,211,77,23,126,52,140,234,128,247,206,133,105,180,135,29,2,2,189,128,41,90,9,193])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [16,233,214,196,219,235,118,177,214,211,77,23,126,52,140,234,128,247,206,133,105,180,135,29,2,2,189,128,41,90,9,193]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [16,233,214,196,219,235,118,177,214,211,77,23,126,52,140,234,128,247,206,133,105,180,135,29,2,2,189,128,41,90,9,193])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 960) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 1280 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 960 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 2049#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 960 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value030) :=
    JGm_TX2_View.value (s00 s) indices00 values00 960 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=960#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠2049#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2921#u32,JGm_TX2_View.index (s00 s) indices00 values00 960 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s00 s).«at» 992#usize)=ok (encodeState (JGc_TX2_HashBytes.state [249,97,95,72,195,239,230,133,231,204,195,159,197,242,53,210,181,126,161,238,155,106,151,110,88,108,146,232,8,121,248,62])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes2 0#usize 0#usize 1#usize 992#usize 2880#usize
    2049#u32 (encodeState value030) (encodeState (JGc_TX2_HashBytes.state [249,97,95,72,195,239,230,133,231,204,195,159,197,242,53,210,181,126,161,238,155,106,151,110,88,108,146,232,8,121,248,62])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read00
  simp only [show 2049#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls2.source040 D hash (s00 s) 1#usize 992#usize 2049#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 992 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 960 v00
      2049#u32 0#usize (encodeState value040) 992#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 2921#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 992 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value031) :=
    JGm_TX2_View.value (s01 s) indices01 values01 992 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=992#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠2921#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨4610#u32,JGm_TX2_View.index (s01 s) indices01 values01 992 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s01 s).«at» 1024#usize)=ok (encodeState (JGc_TX2_HashBytes.state [179,62,84,67,145,245,19,145,0,76,183,216,254,164,78,100,235,197,149,22,181,176,111,192,90,35,170,224,190,165,169,130])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes2 1#usize 1#usize 2#usize 1024#usize 2848#usize
    2921#u32 (encodeState value031) (encodeState (JGc_TX2_HashBytes.state [179,62,84,67,145,245,19,145,0,76,183,216,254,164,78,100,235,197,149,22,181,176,111,192,90,35,170,224,190,165,169,130])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read01
  simp only [show 2921#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls2.source041 D hash (s01 s) 2#usize 1024#usize 2921#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 1024 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 992 v01
      2921#u32 1#usize (encodeState value041) 1024#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 4610#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 1024 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value032) :=
    JGm_TX2_View.value (s02 s) indices02 values02 1024 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=1024#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠4610#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨4994#u32,JGm_TX2_View.index (s02 s) indices02 values02 1024 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s02 s).«at» 1056#usize)=ok (encodeState (JGc_TX2_HashBytes.state [169,21,194,86,169,83,68,57,145,59,224,82,4,255,183,95,137,88,198,233,243,230,177,89,132,186,175,162,5,209,79,171])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes2 2#usize 2#usize 3#usize 1056#usize 2816#usize
    4610#u32 (encodeState value032) (encodeState (JGc_TX2_HashBytes.state [169,21,194,86,169,83,68,57,145,59,224,82,4,255,183,95,137,88,198,233,243,230,177,89,132,186,175,162,5,209,79,171])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read02
  simp only [show 4610#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls2.source042 D hash (s02 s) 3#usize 1056#usize 4610#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 1056 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 1024 v02
      4610#u32 2#usize (encodeState value042) 1056#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 4994#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 1056 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value033) :=
    JGm_TX2_View.value (s03 s) indices03 values03 1056 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=1056#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠4994#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨5745#u32,JGm_TX2_View.index (s03 s) indices03 values03 1056 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s03 s).«at» 1088#usize)=ok (encodeState (JGc_TX2_HashBytes.state [249,125,104,173,124,225,131,121,245,201,10,19,165,30,103,92,67,162,190,80,0,142,172,114,183,72,182,186,237,7,60,125])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes2 3#usize 3#usize 4#usize 1088#usize 2784#usize
    4994#u32 (encodeState value033) (encodeState (JGc_TX2_HashBytes.state [249,125,104,173,124,225,131,121,245,201,10,19,165,30,103,92,67,162,190,80,0,142,172,114,183,72,182,186,237,7,60,125])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read03
  simp only [show 4994#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes2 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls2.source043 D hash (s03 s) 4#usize 1088#usize 4994#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 1088 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 1056 v03
      4994#u32 3#usize (encodeState value043) 1088#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 5745#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 1088 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value034) :=
    JGm_TX2_View.value (s04 s) indices04 values04 1088 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=1088#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠5745#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨6009#u32,JGm_TX2_View.index (s04 s) indices04 values04 1088 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s04 s).«at» 1120#usize)=ok (encodeState (JGc_TX2_HashBytes.state [195,11,91,13,242,157,237,14,230,48,53,152,68,28,146,173,39,23,72,54,22,225,121,215,107,229,54,60,170,68,238,72])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes2 4#usize 4#usize 5#usize 1120#usize 2752#usize
    5745#u32 (encodeState value034) (encodeState (JGc_TX2_HashBytes.state [195,11,91,13,242,157,237,14,230,48,53,152,68,28,146,173,39,23,72,54,22,225,121,215,107,229,54,60,170,68,238,72])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read04
  simp only [show 5745#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes2 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls2.source044 D hash (s04 s) 5#usize 1120#usize 5745#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 1120 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 1088 v04
      5745#u32 4#usize (encodeState value044) 1120#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 6009#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 1120 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value035) :=
    JGm_TX2_View.value (s05 s) indices05 values05 1120 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=1120#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠6009#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨6034#u32,JGm_TX2_View.index (s05 s) indices05 values05 1120 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s05 s).«at» 1152#usize)=ok (encodeState (JGc_TX2_HashBytes.state [179,112,196,108,44,160,62,125,194,38,29,185,108,215,4,140,11,246,68,159,82,31,45,80,100,31,239,92,243,120,250,219])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes2 5#usize 5#usize 6#usize 1152#usize 2720#usize
    6009#u32 (encodeState value035) (encodeState (JGc_TX2_HashBytes.state [179,112,196,108,44,160,62,125,194,38,29,185,108,215,4,140,11,246,68,159,82,31,45,80,100,31,239,92,243,120,250,219])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read05
  simp only [show 6009#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes2 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls2.source045 D hash (s05 s) 6#usize 1152#usize 6009#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 1152 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 1120 v05
      6009#u32 5#usize (encodeState value045) 1152#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 6034#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 1152 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value036) :=
    JGm_TX2_View.value (s06 s) indices06 values06 1152 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=1152#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠6034#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨6542#u32,JGm_TX2_View.index (s06 s) indices06 values06 1152 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s06 s).«at» 1184#usize)=ok (encodeState (JGc_TX2_HashBytes.state [62,167,250,165,65,31,182,78,176,251,194,75,161,83,115,3,81,118,25,197,64,0,255,47,232,78,185,56,42,93,69,86])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes2 6#usize 6#usize 7#usize 1184#usize 2688#usize
    6034#u32 (encodeState value036) (encodeState (JGc_TX2_HashBytes.state [62,167,250,165,65,31,182,78,176,251,194,75,161,83,115,3,81,118,25,197,64,0,255,47,232,78,185,56,42,93,69,86])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read06
  simp only [show 6034#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes2 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls2.source046 D hash (s06 s) 7#usize 1184#usize 6034#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 1184 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 1152 v06
      6034#u32 6#usize (encodeState value046) 1184#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 6542#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 1184 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value037) :=
    JGm_TX2_View.value (s07 s) indices07 values07 1184 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=1184#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠6542#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨6775#u32,JGm_TX2_View.index (s07 s) indices07 values07 1184 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s07 s).«at» 1216#usize)=ok (encodeState (JGc_TX2_HashBytes.state [57,54,77,49,101,42,95,108,7,193,128,156,160,108,172,205,176,94,234,119,178,60,14,61,107,83,83,99,46,128,55,36])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes2 7#usize 7#usize 8#usize 1216#usize 2656#usize
    6542#u32 (encodeState value037) (encodeState (JGc_TX2_HashBytes.state [57,54,77,49,101,42,95,108,7,193,128,156,160,108,172,205,176,94,234,119,178,60,14,61,107,83,83,99,46,128,55,36])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read07
  simp only [show 6542#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes2 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls2.source047 D hash (s07 s) 8#usize 1216#usize 6542#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 1216 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 1184 v07
      6542#u32 7#usize (encodeState value047) 1216#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 6775#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 1216 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value038) :=
    JGm_TX2_View.value (s08 s) indices08 values08 1216 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=1216#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠6775#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨7684#u32,JGm_TX2_View.index (s08 s) indices08 values08 1216 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s08 s).«at» 1248#usize)=ok (encodeState (JGc_TX2_HashBytes.state [162,78,44,26,160,83,123,134,218,232,6,213,29,159,101,194,116,107,147,229,122,88,91,82,166,42,5,120,181,179,197,167])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes2 8#usize 8#usize 9#usize 1248#usize 2624#usize
    6775#u32 (encodeState value038) (encodeState (JGc_TX2_HashBytes.state [162,78,44,26,160,83,123,134,218,232,6,213,29,159,101,194,116,107,147,229,122,88,91,82,166,42,5,120,181,179,197,167])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read08
  simp only [show 6775#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes2 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls2.source048 D hash (s08 s) 9#usize 1248#usize 6775#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 1248 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 1216 v08
      6775#u32 8#usize (encodeState value048) 1248#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 7684#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 1248 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value039) :=
    JGm_TX2_View.value (s09 s) indices09 values09 1248 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=1248#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠7684#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s09 s).«at» 1280#usize)=ok (encodeState (JGc_TX2_HashBytes.state [16,233,214,196,219,235,118,177,214,211,77,23,126,52,140,234,128,247,206,133,105,180,135,29,2,2,189,128,41,90,9,193])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes2 9#usize 9#usize 10#usize 1280#usize 2592#usize
    7684#u32 (encodeState value039) (encodeState (JGc_TX2_HashBytes.state [16,233,214,196,219,235,118,177,214,211,77,23,126,52,140,234,128,247,206,133,105,180,135,29,2,2,189,128,41,90,9,193])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read09
  simp only [show 7684#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes2 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls2.source049 D hash (s09 s) 10#usize 1280#usize 7684#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 1280 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 1248 v09
      7684#u32 9#usize (encodeState value049) 1280#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes2 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes2 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes2 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes2 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes2 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes2 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes2 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes2 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes2 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 1280
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level2_03
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level2_04
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes2
def indices00 : List U32 := [1024#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
def values00 : List (Array U8 32#usize) := [encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 1024#u32 0#usize (encodeState value050) 1312#usize
 def indices01 : List U32 := [512#u32,1460#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value050,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 1460#u32 1#usize (encodeState value051) 1344#usize
 def indices02 : List U32 := [512#u32,730#u32,2305#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 2305#u32 2#usize (encodeState value052) 1376#usize
 def indices03 : List U32 := [512#u32,730#u32,1152#u32,2497#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 2497#u32 3#usize (encodeState value053) 1408#usize
 def indices04 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,2872#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value044,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 2872#u32 4#usize (encodeState value054) 1440#usize
 def indices05 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,3004#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value045,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 3004#u32 5#usize (encodeState value055) 1472#usize
 def indices06 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,3017#u32,3271#u32,3387#u32,3842#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value046,encodeState value047,encodeState value048,encodeState value049]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 3017#u32 6#usize (encodeState value056) 1504#usize
 def indices07 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,3271#u32,3387#u32,3842#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value047,encodeState value048,encodeState value049]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 3271#u32 7#usize (encodeState value057) 1536#usize
 def indices08 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,3387#u32,3842#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value048,encodeState value049]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 3387#u32 8#usize (encodeState value058) 1568#usize
 def indices09 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,3842#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value049]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 3842#u32 9#usize (encodeState value059) 1600#usize
 def indices10 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1280#usize 1312#usize)=ok (encodeState (JGc_TX2_HashBytes.state [65,234,38,73,66,178,230,20,65,121,30,37,225,239,162,80,19,158,198,194,173,16,25,109,108,151,246,72,8,249,139,52])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1280#usize 1312#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1280#usize 1312#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [65,234,38,73,66,178,230,20,65,121,30,37,225,239,162,80,19,158,198,194,173,16,25,109,108,151,246,72,8,249,139,52])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1280).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38983).take 32)=(encodeState (JGc_TX2_HashBytes.state [65,234,38,73,66,178,230,20,65,121,30,37,225,239,162,80,19,158,198,194,173,16,25,109,108,151,246,72,8,249,139,52])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1280#usize 1312#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [65,234,38,73,66,178,230,20,65,121,30,37,225,239,162,80,19,158,198,194,173,16,25,109,108,151,246,72,8,249,139,52])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [65,234,38,73,66,178,230,20,65,121,30,37,225,239,162,80,19,158,198,194,173,16,25,109,108,151,246,72,8,249,139,52]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [65,234,38,73,66,178,230,20,65,121,30,37,225,239,162,80,19,158,198,194,173,16,25,109,108,151,246,72,8,249,139,52])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1312#usize 1344#usize)=ok (encodeState (JGc_TX2_HashBytes.state [160,196,206,167,250,112,3,28,143,138,174,230,166,61,96,100,21,194,32,169,75,99,235,184,138,126,251,198,150,238,190,52])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1312#usize 1344#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1312#usize 1344#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [160,196,206,167,250,112,3,28,143,138,174,230,166,61,96,100,21,194,32,169,75,99,235,184,138,126,251,198,150,238,190,52])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1312).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39015).take 32)=(encodeState (JGc_TX2_HashBytes.state [160,196,206,167,250,112,3,28,143,138,174,230,166,61,96,100,21,194,32,169,75,99,235,184,138,126,251,198,150,238,190,52])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1312#usize 1344#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [160,196,206,167,250,112,3,28,143,138,174,230,166,61,96,100,21,194,32,169,75,99,235,184,138,126,251,198,150,238,190,52])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [160,196,206,167,250,112,3,28,143,138,174,230,166,61,96,100,21,194,32,169,75,99,235,184,138,126,251,198,150,238,190,52]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [160,196,206,167,250,112,3,28,143,138,174,230,166,61,96,100,21,194,32,169,75,99,235,184,138,126,251,198,150,238,190,52])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1344#usize 1376#usize)=ok (encodeState (JGc_TX2_HashBytes.state [116,149,89,253,254,19,246,16,170,116,173,230,189,196,143,72,229,205,60,207,4,27,195,29,163,34,89,116,252,50,119,14])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1344#usize 1376#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1344#usize 1376#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [116,149,89,253,254,19,246,16,170,116,173,230,189,196,143,72,229,205,60,207,4,27,195,29,163,34,89,116,252,50,119,14])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1344).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39047).take 32)=(encodeState (JGc_TX2_HashBytes.state [116,149,89,253,254,19,246,16,170,116,173,230,189,196,143,72,229,205,60,207,4,27,195,29,163,34,89,116,252,50,119,14])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1344#usize 1376#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [116,149,89,253,254,19,246,16,170,116,173,230,189,196,143,72,229,205,60,207,4,27,195,29,163,34,89,116,252,50,119,14])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [116,149,89,253,254,19,246,16,170,116,173,230,189,196,143,72,229,205,60,207,4,27,195,29,163,34,89,116,252,50,119,14]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [116,149,89,253,254,19,246,16,170,116,173,230,189,196,143,72,229,205,60,207,4,27,195,29,163,34,89,116,252,50,119,14])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1376#usize 1408#usize)=ok (encodeState (JGc_TX2_HashBytes.state [55,78,39,200,76,202,7,1,140,171,82,253,129,15,177,0,61,7,55,23,33,240,211,141,37,123,101,117,182,39,64,187])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1376#usize 1408#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1376#usize 1408#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [55,78,39,200,76,202,7,1,140,171,82,253,129,15,177,0,61,7,55,23,33,240,211,141,37,123,101,117,182,39,64,187])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1376).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39079).take 32)=(encodeState (JGc_TX2_HashBytes.state [55,78,39,200,76,202,7,1,140,171,82,253,129,15,177,0,61,7,55,23,33,240,211,141,37,123,101,117,182,39,64,187])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1376#usize 1408#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [55,78,39,200,76,202,7,1,140,171,82,253,129,15,177,0,61,7,55,23,33,240,211,141,37,123,101,117,182,39,64,187])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [55,78,39,200,76,202,7,1,140,171,82,253,129,15,177,0,61,7,55,23,33,240,211,141,37,123,101,117,182,39,64,187]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [55,78,39,200,76,202,7,1,140,171,82,253,129,15,177,0,61,7,55,23,33,240,211,141,37,123,101,117,182,39,64,187])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1408#usize 1440#usize)=ok (encodeState (JGc_TX2_HashBytes.state [214,125,42,28,128,37,83,168,43,239,170,218,176,52,50,65,50,39,88,130,133,76,132,84,182,217,3,23,118,224,99,151])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1408#usize 1440#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1408#usize 1440#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [214,125,42,28,128,37,83,168,43,239,170,218,176,52,50,65,50,39,88,130,133,76,132,84,182,217,3,23,118,224,99,151])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1408).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39111).take 32)=(encodeState (JGc_TX2_HashBytes.state [214,125,42,28,128,37,83,168,43,239,170,218,176,52,50,65,50,39,88,130,133,76,132,84,182,217,3,23,118,224,99,151])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1408#usize 1440#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [214,125,42,28,128,37,83,168,43,239,170,218,176,52,50,65,50,39,88,130,133,76,132,84,182,217,3,23,118,224,99,151])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [214,125,42,28,128,37,83,168,43,239,170,218,176,52,50,65,50,39,88,130,133,76,132,84,182,217,3,23,118,224,99,151]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [214,125,42,28,128,37,83,168,43,239,170,218,176,52,50,65,50,39,88,130,133,76,132,84,182,217,3,23,118,224,99,151])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1440#usize 1472#usize)=ok (encodeState (JGc_TX2_HashBytes.state [59,77,103,151,197,77,27,177,181,138,84,152,90,178,108,53,229,207,203,146,23,110,171,197,65,83,20,196,13,21,172,117])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1440#usize 1472#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1440#usize 1472#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [59,77,103,151,197,77,27,177,181,138,84,152,90,178,108,53,229,207,203,146,23,110,171,197,65,83,20,196,13,21,172,117])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1440).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39143).take 32)=(encodeState (JGc_TX2_HashBytes.state [59,77,103,151,197,77,27,177,181,138,84,152,90,178,108,53,229,207,203,146,23,110,171,197,65,83,20,196,13,21,172,117])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1440#usize 1472#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [59,77,103,151,197,77,27,177,181,138,84,152,90,178,108,53,229,207,203,146,23,110,171,197,65,83,20,196,13,21,172,117])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [59,77,103,151,197,77,27,177,181,138,84,152,90,178,108,53,229,207,203,146,23,110,171,197,65,83,20,196,13,21,172,117]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [59,77,103,151,197,77,27,177,181,138,84,152,90,178,108,53,229,207,203,146,23,110,171,197,65,83,20,196,13,21,172,117])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1472#usize 1504#usize)=ok (encodeState (JGc_TX2_HashBytes.state [121,155,170,137,92,23,153,245,180,227,87,14,77,237,32,32,201,175,78,100,37,206,227,60,30,169,227,45,145,173,245,195])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1472#usize 1504#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1472#usize 1504#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [121,155,170,137,92,23,153,245,180,227,87,14,77,237,32,32,201,175,78,100,37,206,227,60,30,169,227,45,145,173,245,195])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1472).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39175).take 32)=(encodeState (JGc_TX2_HashBytes.state [121,155,170,137,92,23,153,245,180,227,87,14,77,237,32,32,201,175,78,100,37,206,227,60,30,169,227,45,145,173,245,195])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1472#usize 1504#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [121,155,170,137,92,23,153,245,180,227,87,14,77,237,32,32,201,175,78,100,37,206,227,60,30,169,227,45,145,173,245,195])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [121,155,170,137,92,23,153,245,180,227,87,14,77,237,32,32,201,175,78,100,37,206,227,60,30,169,227,45,145,173,245,195]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [121,155,170,137,92,23,153,245,180,227,87,14,77,237,32,32,201,175,78,100,37,206,227,60,30,169,227,45,145,173,245,195])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1504#usize 1536#usize)=ok (encodeState (JGc_TX2_HashBytes.state [77,20,168,204,126,214,237,104,69,211,193,212,69,14,169,89,19,73,26,130,68,35,49,151,26,120,232,187,43,24,108,230])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1504#usize 1536#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1504#usize 1536#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [77,20,168,204,126,214,237,104,69,211,193,212,69,14,169,89,19,73,26,130,68,35,49,151,26,120,232,187,43,24,108,230])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1504).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39207).take 32)=(encodeState (JGc_TX2_HashBytes.state [77,20,168,204,126,214,237,104,69,211,193,212,69,14,169,89,19,73,26,130,68,35,49,151,26,120,232,187,43,24,108,230])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1504#usize 1536#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [77,20,168,204,126,214,237,104,69,211,193,212,69,14,169,89,19,73,26,130,68,35,49,151,26,120,232,187,43,24,108,230])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [77,20,168,204,126,214,237,104,69,211,193,212,69,14,169,89,19,73,26,130,68,35,49,151,26,120,232,187,43,24,108,230]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [77,20,168,204,126,214,237,104,69,211,193,212,69,14,169,89,19,73,26,130,68,35,49,151,26,120,232,187,43,24,108,230])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1536#usize 1568#usize)=ok (encodeState (JGc_TX2_HashBytes.state [219,113,206,154,96,101,14,206,79,208,91,12,62,43,111,15,159,175,162,128,58,189,130,180,129,14,209,29,246,135,107,199])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1536#usize 1568#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1536#usize 1568#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [219,113,206,154,96,101,14,206,79,208,91,12,62,43,111,15,159,175,162,128,58,189,130,180,129,14,209,29,246,135,107,199])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1536).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39239).take 32)=(encodeState (JGc_TX2_HashBytes.state [219,113,206,154,96,101,14,206,79,208,91,12,62,43,111,15,159,175,162,128,58,189,130,180,129,14,209,29,246,135,107,199])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1536#usize 1568#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [219,113,206,154,96,101,14,206,79,208,91,12,62,43,111,15,159,175,162,128,58,189,130,180,129,14,209,29,246,135,107,199])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [219,113,206,154,96,101,14,206,79,208,91,12,62,43,111,15,159,175,162,128,58,189,130,180,129,14,209,29,246,135,107,199]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [219,113,206,154,96,101,14,206,79,208,91,12,62,43,111,15,159,175,162,128,58,189,130,180,129,14,209,29,246,135,107,199])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1568#usize 1600#usize)=ok (encodeState (JGc_TX2_HashBytes.state [179,218,162,212,20,131,120,109,52,129,111,92,132,18,158,30,184,98,130,212,185,233,158,145,127,59,221,46,0,214,80,21])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1568#usize 1600#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1568#usize 1600#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [179,218,162,212,20,131,120,109,52,129,111,92,132,18,158,30,184,98,130,212,185,233,158,145,127,59,221,46,0,214,80,21])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1568).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39271).take 32)=(encodeState (JGc_TX2_HashBytes.state [179,218,162,212,20,131,120,109,52,129,111,92,132,18,158,30,184,98,130,212,185,233,158,145,127,59,221,46,0,214,80,21])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1568#usize 1600#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [179,218,162,212,20,131,120,109,52,129,111,92,132,18,158,30,184,98,130,212,185,233,158,145,127,59,221,46,0,214,80,21])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [179,218,162,212,20,131,120,109,52,129,111,92,132,18,158,30,184,98,130,212,185,233,158,145,127,59,221,46,0,214,80,21]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [179,218,162,212,20,131,120,109,52,129,111,92,132,18,158,30,184,98,130,212,185,233,158,145,127,59,221,46,0,214,80,21])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 1280) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 1600 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 1280 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 1024#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 1280 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value040) :=
    JGm_TX2_View.value (s00 s) indices00 values00 1280 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=1280#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠1024#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1460#u32,JGm_TX2_View.index (s00 s) indices00 values00 1280 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s00 s).«at» 1312#usize)=ok (encodeState (JGc_TX2_HashBytes.state [65,234,38,73,66,178,230,20,65,121,30,37,225,239,162,80,19,158,198,194,173,16,25,109,108,151,246,72,8,249,139,52])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes2 0#usize 0#usize 1#usize 1312#usize 2560#usize
    1024#u32 (encodeState value040) (encodeState (JGc_TX2_HashBytes.state [65,234,38,73,66,178,230,20,65,121,30,37,225,239,162,80,19,158,198,194,173,16,25,109,108,151,246,72,8,249,139,52])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read00
  simp only [show 1024#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls2.source050 D hash (s00 s) 1#usize 1312#usize 1024#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 1312 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 1280 v00
      1024#u32 0#usize (encodeState value050) 1312#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 1460#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 1312 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value041) :=
    JGm_TX2_View.value (s01 s) indices01 values01 1312 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=1312#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠1460#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2305#u32,JGm_TX2_View.index (s01 s) indices01 values01 1312 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s01 s).«at» 1344#usize)=ok (encodeState (JGc_TX2_HashBytes.state [160,196,206,167,250,112,3,28,143,138,174,230,166,61,96,100,21,194,32,169,75,99,235,184,138,126,251,198,150,238,190,52])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes2 1#usize 1#usize 2#usize 1344#usize 2528#usize
    1460#u32 (encodeState value041) (encodeState (JGc_TX2_HashBytes.state [160,196,206,167,250,112,3,28,143,138,174,230,166,61,96,100,21,194,32,169,75,99,235,184,138,126,251,198,150,238,190,52])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read01
  simp only [show 1460#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls2.source051 D hash (s01 s) 2#usize 1344#usize 1460#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 1344 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 1312 v01
      1460#u32 1#usize (encodeState value051) 1344#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 2305#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 1344 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value042) :=
    JGm_TX2_View.value (s02 s) indices02 values02 1344 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=1344#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠2305#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2497#u32,JGm_TX2_View.index (s02 s) indices02 values02 1344 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s02 s).«at» 1376#usize)=ok (encodeState (JGc_TX2_HashBytes.state [116,149,89,253,254,19,246,16,170,116,173,230,189,196,143,72,229,205,60,207,4,27,195,29,163,34,89,116,252,50,119,14])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes2 2#usize 2#usize 3#usize 1376#usize 2496#usize
    2305#u32 (encodeState value042) (encodeState (JGc_TX2_HashBytes.state [116,149,89,253,254,19,246,16,170,116,173,230,189,196,143,72,229,205,60,207,4,27,195,29,163,34,89,116,252,50,119,14])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read02
  simp only [show 2305#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls2.source052 D hash (s02 s) 3#usize 1376#usize 2305#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 1376 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 1344 v02
      2305#u32 2#usize (encodeState value052) 1376#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 2497#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 1376 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value043) :=
    JGm_TX2_View.value (s03 s) indices03 values03 1376 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=1376#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠2497#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2872#u32,JGm_TX2_View.index (s03 s) indices03 values03 1376 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s03 s).«at» 1408#usize)=ok (encodeState (JGc_TX2_HashBytes.state [55,78,39,200,76,202,7,1,140,171,82,253,129,15,177,0,61,7,55,23,33,240,211,141,37,123,101,117,182,39,64,187])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes2 3#usize 3#usize 4#usize 1408#usize 2464#usize
    2497#u32 (encodeState value043) (encodeState (JGc_TX2_HashBytes.state [55,78,39,200,76,202,7,1,140,171,82,253,129,15,177,0,61,7,55,23,33,240,211,141,37,123,101,117,182,39,64,187])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read03
  simp only [show 2497#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes2 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls2.source053 D hash (s03 s) 4#usize 1408#usize 2497#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 1408 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 1376 v03
      2497#u32 3#usize (encodeState value053) 1408#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 2872#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 1408 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value044) :=
    JGm_TX2_View.value (s04 s) indices04 values04 1408 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=1408#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠2872#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3004#u32,JGm_TX2_View.index (s04 s) indices04 values04 1408 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s04 s).«at» 1440#usize)=ok (encodeState (JGc_TX2_HashBytes.state [214,125,42,28,128,37,83,168,43,239,170,218,176,52,50,65,50,39,88,130,133,76,132,84,182,217,3,23,118,224,99,151])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes2 4#usize 4#usize 5#usize 1440#usize 2432#usize
    2872#u32 (encodeState value044) (encodeState (JGc_TX2_HashBytes.state [214,125,42,28,128,37,83,168,43,239,170,218,176,52,50,65,50,39,88,130,133,76,132,84,182,217,3,23,118,224,99,151])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read04
  simp only [show 2872#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes2 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls2.source054 D hash (s04 s) 5#usize 1440#usize 2872#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 1440 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 1408 v04
      2872#u32 4#usize (encodeState value054) 1440#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 3004#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 1440 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value045) :=
    JGm_TX2_View.value (s05 s) indices05 values05 1440 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=1440#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠3004#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3017#u32,JGm_TX2_View.index (s05 s) indices05 values05 1440 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s05 s).«at» 1472#usize)=ok (encodeState (JGc_TX2_HashBytes.state [59,77,103,151,197,77,27,177,181,138,84,152,90,178,108,53,229,207,203,146,23,110,171,197,65,83,20,196,13,21,172,117])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes2 5#usize 5#usize 6#usize 1472#usize 2400#usize
    3004#u32 (encodeState value045) (encodeState (JGc_TX2_HashBytes.state [59,77,103,151,197,77,27,177,181,138,84,152,90,178,108,53,229,207,203,146,23,110,171,197,65,83,20,196,13,21,172,117])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read05
  simp only [show 3004#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes2 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls2.source055 D hash (s05 s) 6#usize 1472#usize 3004#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 1472 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 1440 v05
      3004#u32 5#usize (encodeState value055) 1472#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 3017#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 1472 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value046) :=
    JGm_TX2_View.value (s06 s) indices06 values06 1472 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=1472#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠3017#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3271#u32,JGm_TX2_View.index (s06 s) indices06 values06 1472 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s06 s).«at» 1504#usize)=ok (encodeState (JGc_TX2_HashBytes.state [121,155,170,137,92,23,153,245,180,227,87,14,77,237,32,32,201,175,78,100,37,206,227,60,30,169,227,45,145,173,245,195])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes2 6#usize 6#usize 7#usize 1504#usize 2368#usize
    3017#u32 (encodeState value046) (encodeState (JGc_TX2_HashBytes.state [121,155,170,137,92,23,153,245,180,227,87,14,77,237,32,32,201,175,78,100,37,206,227,60,30,169,227,45,145,173,245,195])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read06
  simp only [show 3017#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes2 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls2.source056 D hash (s06 s) 7#usize 1504#usize 3017#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 1504 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 1472 v06
      3017#u32 6#usize (encodeState value056) 1504#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 3271#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 1504 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value047) :=
    JGm_TX2_View.value (s07 s) indices07 values07 1504 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=1504#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠3271#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3387#u32,JGm_TX2_View.index (s07 s) indices07 values07 1504 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s07 s).«at» 1536#usize)=ok (encodeState (JGc_TX2_HashBytes.state [77,20,168,204,126,214,237,104,69,211,193,212,69,14,169,89,19,73,26,130,68,35,49,151,26,120,232,187,43,24,108,230])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes2 7#usize 7#usize 8#usize 1536#usize 2336#usize
    3271#u32 (encodeState value047) (encodeState (JGc_TX2_HashBytes.state [77,20,168,204,126,214,237,104,69,211,193,212,69,14,169,89,19,73,26,130,68,35,49,151,26,120,232,187,43,24,108,230])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read07
  simp only [show 3271#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes2 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls2.source057 D hash (s07 s) 8#usize 1536#usize 3271#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 1536 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 1504 v07
      3271#u32 7#usize (encodeState value057) 1536#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 3387#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 1536 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value048) :=
    JGm_TX2_View.value (s08 s) indices08 values08 1536 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=1536#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠3387#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3842#u32,JGm_TX2_View.index (s08 s) indices08 values08 1536 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s08 s).«at» 1568#usize)=ok (encodeState (JGc_TX2_HashBytes.state [219,113,206,154,96,101,14,206,79,208,91,12,62,43,111,15,159,175,162,128,58,189,130,180,129,14,209,29,246,135,107,199])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes2 8#usize 8#usize 9#usize 1568#usize 2304#usize
    3387#u32 (encodeState value048) (encodeState (JGc_TX2_HashBytes.state [219,113,206,154,96,101,14,206,79,208,91,12,62,43,111,15,159,175,162,128,58,189,130,180,129,14,209,29,246,135,107,199])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read08
  simp only [show 3387#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes2 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls2.source058 D hash (s08 s) 9#usize 1568#usize 3387#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 1568 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 1536 v08
      3387#u32 8#usize (encodeState value058) 1568#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 3842#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 1568 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value049) :=
    JGm_TX2_View.value (s09 s) indices09 values09 1568 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=1568#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠3842#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s09 s).«at» 1600#usize)=ok (encodeState (JGc_TX2_HashBytes.state [179,218,162,212,20,131,120,109,52,129,111,92,132,18,158,30,184,98,130,212,185,233,158,145,127,59,221,46,0,214,80,21])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes2 9#usize 9#usize 10#usize 1600#usize 2272#usize
    3842#u32 (encodeState value049) (encodeState (JGc_TX2_HashBytes.state [179,218,162,212,20,131,120,109,52,129,111,92,132,18,158,30,184,98,130,212,185,233,158,145,127,59,221,46,0,214,80,21])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read09
  simp only [show 3842#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes2 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls2.source059 D hash (s09 s) 10#usize 1600#usize 3842#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 1600 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 1568 v09
      3842#u32 9#usize (encodeState value059) 1600#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes2 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes2 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes2 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes2 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes2 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes2 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes2 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes2 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes2 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 1600
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level2_04
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level2_05
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes2
def indices00 : List U32 := [512#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
def values00 : List (Array U8 32#usize) := [encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 512#u32 0#usize (encodeState value060) 1632#usize
 def indices01 : List U32 := [256#u32,730#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value060,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 730#u32 1#usize (encodeState value061) 1664#usize
 def indices02 : List U32 := [256#u32,365#u32,1152#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 1152#u32 2#usize (encodeState value062) 1696#usize
 def indices03 : List U32 := [256#u32,365#u32,576#u32,1248#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 1248#u32 3#usize (encodeState value063) 1728#usize
 def indices04 : List U32 := [256#u32,365#u32,576#u32,624#u32,1436#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 1436#u32 4#usize (encodeState value064) 1760#usize
 def indices05 : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,1502#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 1502#u32 5#usize (encodeState value065) 1792#usize
 def indices06 : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,751#u32,1508#u32,1635#u32,1693#u32,1921#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 1508#u32 6#usize (encodeState value066) 1824#usize
 def indices07 : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,751#u32,754#u32,1635#u32,1693#u32,1921#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value057,encodeState value058,encodeState value059]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 1635#u32 7#usize (encodeState value067) 1856#usize
 def indices08 : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,751#u32,754#u32,817#u32,1693#u32,1921#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value058,encodeState value059]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 1693#u32 8#usize (encodeState value068) 1888#usize
 def indices09 : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,751#u32,754#u32,817#u32,846#u32,1921#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value059]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 1921#u32 9#usize (encodeState value069) 1920#usize
 def indices10 : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,751#u32,754#u32,817#u32,846#u32,960#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [256#u32,365#u32,576#u32,624#u32,718#u32,751#u32,754#u32,817#u32,846#u32,960#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1600#usize 1632#usize)=ok (encodeState (JGc_TX2_HashBytes.state [125,62,11,58,152,121,161,20,87,123,59,146,157,58,136,241,164,159,33,232,66,172,208,243,124,111,180,225,182,173,183,11])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1600#usize 1632#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1600#usize 1632#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [125,62,11,58,152,121,161,20,87,123,59,146,157,58,136,241,164,159,33,232,66,172,208,243,124,111,180,225,182,173,183,11])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1600).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39303).take 32)=(encodeState (JGc_TX2_HashBytes.state [125,62,11,58,152,121,161,20,87,123,59,146,157,58,136,241,164,159,33,232,66,172,208,243,124,111,180,225,182,173,183,11])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1600#usize 1632#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [125,62,11,58,152,121,161,20,87,123,59,146,157,58,136,241,164,159,33,232,66,172,208,243,124,111,180,225,182,173,183,11])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [125,62,11,58,152,121,161,20,87,123,59,146,157,58,136,241,164,159,33,232,66,172,208,243,124,111,180,225,182,173,183,11]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [125,62,11,58,152,121,161,20,87,123,59,146,157,58,136,241,164,159,33,232,66,172,208,243,124,111,180,225,182,173,183,11])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1632#usize 1664#usize)=ok (encodeState (JGc_TX2_HashBytes.state [108,85,227,67,255,107,240,217,131,85,181,219,24,10,252,188,214,141,198,133,159,73,116,15,37,35,242,27,251,66,11,3])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1632#usize 1664#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1632#usize 1664#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [108,85,227,67,255,107,240,217,131,85,181,219,24,10,252,188,214,141,198,133,159,73,116,15,37,35,242,27,251,66,11,3])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1632).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39335).take 32)=(encodeState (JGc_TX2_HashBytes.state [108,85,227,67,255,107,240,217,131,85,181,219,24,10,252,188,214,141,198,133,159,73,116,15,37,35,242,27,251,66,11,3])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1632#usize 1664#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [108,85,227,67,255,107,240,217,131,85,181,219,24,10,252,188,214,141,198,133,159,73,116,15,37,35,242,27,251,66,11,3])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [108,85,227,67,255,107,240,217,131,85,181,219,24,10,252,188,214,141,198,133,159,73,116,15,37,35,242,27,251,66,11,3]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [108,85,227,67,255,107,240,217,131,85,181,219,24,10,252,188,214,141,198,133,159,73,116,15,37,35,242,27,251,66,11,3])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1664#usize 1696#usize)=ok (encodeState (JGc_TX2_HashBytes.state [20,69,131,244,4,224,142,147,45,30,160,115,55,150,86,41,62,233,146,3,5,126,120,19,244,204,58,53,181,84,196,197])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1664#usize 1696#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1664#usize 1696#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [20,69,131,244,4,224,142,147,45,30,160,115,55,150,86,41,62,233,146,3,5,126,120,19,244,204,58,53,181,84,196,197])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1664).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39367).take 32)=(encodeState (JGc_TX2_HashBytes.state [20,69,131,244,4,224,142,147,45,30,160,115,55,150,86,41,62,233,146,3,5,126,120,19,244,204,58,53,181,84,196,197])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1664#usize 1696#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [20,69,131,244,4,224,142,147,45,30,160,115,55,150,86,41,62,233,146,3,5,126,120,19,244,204,58,53,181,84,196,197])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [20,69,131,244,4,224,142,147,45,30,160,115,55,150,86,41,62,233,146,3,5,126,120,19,244,204,58,53,181,84,196,197]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [20,69,131,244,4,224,142,147,45,30,160,115,55,150,86,41,62,233,146,3,5,126,120,19,244,204,58,53,181,84,196,197])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1696#usize 1728#usize)=ok (encodeState (JGc_TX2_HashBytes.state [46,207,213,156,44,97,223,5,239,95,131,76,225,10,249,132,169,237,91,238,24,122,79,76,77,172,35,29,240,46,161,81])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1696#usize 1728#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1696#usize 1728#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [46,207,213,156,44,97,223,5,239,95,131,76,225,10,249,132,169,237,91,238,24,122,79,76,77,172,35,29,240,46,161,81])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1696).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39399).take 32)=(encodeState (JGc_TX2_HashBytes.state [46,207,213,156,44,97,223,5,239,95,131,76,225,10,249,132,169,237,91,238,24,122,79,76,77,172,35,29,240,46,161,81])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1696#usize 1728#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [46,207,213,156,44,97,223,5,239,95,131,76,225,10,249,132,169,237,91,238,24,122,79,76,77,172,35,29,240,46,161,81])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [46,207,213,156,44,97,223,5,239,95,131,76,225,10,249,132,169,237,91,238,24,122,79,76,77,172,35,29,240,46,161,81]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [46,207,213,156,44,97,223,5,239,95,131,76,225,10,249,132,169,237,91,238,24,122,79,76,77,172,35,29,240,46,161,81])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1728#usize 1760#usize)=ok (encodeState (JGc_TX2_HashBytes.state [95,12,139,86,115,166,43,216,121,70,107,251,72,70,51,33,19,180,64,129,152,241,136,194,104,235,4,19,207,59,71,38])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1728#usize 1760#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1728#usize 1760#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [95,12,139,86,115,166,43,216,121,70,107,251,72,70,51,33,19,180,64,129,152,241,136,194,104,235,4,19,207,59,71,38])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1728).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39431).take 32)=(encodeState (JGc_TX2_HashBytes.state [95,12,139,86,115,166,43,216,121,70,107,251,72,70,51,33,19,180,64,129,152,241,136,194,104,235,4,19,207,59,71,38])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1728#usize 1760#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [95,12,139,86,115,166,43,216,121,70,107,251,72,70,51,33,19,180,64,129,152,241,136,194,104,235,4,19,207,59,71,38])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [95,12,139,86,115,166,43,216,121,70,107,251,72,70,51,33,19,180,64,129,152,241,136,194,104,235,4,19,207,59,71,38]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [95,12,139,86,115,166,43,216,121,70,107,251,72,70,51,33,19,180,64,129,152,241,136,194,104,235,4,19,207,59,71,38])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1760#usize 1792#usize)=ok (encodeState (JGc_TX2_HashBytes.state [96,144,30,173,153,163,192,34,238,70,42,254,168,235,204,203,30,126,228,206,111,202,34,173,110,50,39,31,76,7,91,117])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1760#usize 1792#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1760#usize 1792#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [96,144,30,173,153,163,192,34,238,70,42,254,168,235,204,203,30,126,228,206,111,202,34,173,110,50,39,31,76,7,91,117])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1760).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39463).take 32)=(encodeState (JGc_TX2_HashBytes.state [96,144,30,173,153,163,192,34,238,70,42,254,168,235,204,203,30,126,228,206,111,202,34,173,110,50,39,31,76,7,91,117])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1760#usize 1792#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [96,144,30,173,153,163,192,34,238,70,42,254,168,235,204,203,30,126,228,206,111,202,34,173,110,50,39,31,76,7,91,117])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [96,144,30,173,153,163,192,34,238,70,42,254,168,235,204,203,30,126,228,206,111,202,34,173,110,50,39,31,76,7,91,117]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [96,144,30,173,153,163,192,34,238,70,42,254,168,235,204,203,30,126,228,206,111,202,34,173,110,50,39,31,76,7,91,117])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1792#usize 1824#usize)=ok (encodeState (JGc_TX2_HashBytes.state [193,40,69,139,235,218,184,141,95,6,104,82,149,17,63,148,181,126,57,142,185,25,231,88,16,185,114,171,2,44,236,81])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1792#usize 1824#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1792#usize 1824#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [193,40,69,139,235,218,184,141,95,6,104,82,149,17,63,148,181,126,57,142,185,25,231,88,16,185,114,171,2,44,236,81])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1792).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39495).take 32)=(encodeState (JGc_TX2_HashBytes.state [193,40,69,139,235,218,184,141,95,6,104,82,149,17,63,148,181,126,57,142,185,25,231,88,16,185,114,171,2,44,236,81])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1792#usize 1824#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [193,40,69,139,235,218,184,141,95,6,104,82,149,17,63,148,181,126,57,142,185,25,231,88,16,185,114,171,2,44,236,81])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [193,40,69,139,235,218,184,141,95,6,104,82,149,17,63,148,181,126,57,142,185,25,231,88,16,185,114,171,2,44,236,81]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [193,40,69,139,235,218,184,141,95,6,104,82,149,17,63,148,181,126,57,142,185,25,231,88,16,185,114,171,2,44,236,81])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1824#usize 1856#usize)=ok (encodeState (JGc_TX2_HashBytes.state [108,244,30,13,4,164,224,60,6,70,5,194,113,19,224,179,103,199,233,246,124,170,2,80,220,146,148,253,253,191,218,219])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1824#usize 1856#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1824#usize 1856#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [108,244,30,13,4,164,224,60,6,70,5,194,113,19,224,179,103,199,233,246,124,170,2,80,220,146,148,253,253,191,218,219])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1824).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39527).take 32)=(encodeState (JGc_TX2_HashBytes.state [108,244,30,13,4,164,224,60,6,70,5,194,113,19,224,179,103,199,233,246,124,170,2,80,220,146,148,253,253,191,218,219])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1824#usize 1856#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [108,244,30,13,4,164,224,60,6,70,5,194,113,19,224,179,103,199,233,246,124,170,2,80,220,146,148,253,253,191,218,219])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [108,244,30,13,4,164,224,60,6,70,5,194,113,19,224,179,103,199,233,246,124,170,2,80,220,146,148,253,253,191,218,219]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [108,244,30,13,4,164,224,60,6,70,5,194,113,19,224,179,103,199,233,246,124,170,2,80,220,146,148,253,253,191,218,219])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1856#usize 1888#usize)=ok (encodeState (JGc_TX2_HashBytes.state [77,83,165,84,145,44,241,189,189,116,178,122,62,239,124,255,41,4,75,96,207,188,221,80,196,143,108,51,218,23,202,213])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1856#usize 1888#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1856#usize 1888#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [77,83,165,84,145,44,241,189,189,116,178,122,62,239,124,255,41,4,75,96,207,188,221,80,196,143,108,51,218,23,202,213])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1856).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39559).take 32)=(encodeState (JGc_TX2_HashBytes.state [77,83,165,84,145,44,241,189,189,116,178,122,62,239,124,255,41,4,75,96,207,188,221,80,196,143,108,51,218,23,202,213])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1856#usize 1888#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [77,83,165,84,145,44,241,189,189,116,178,122,62,239,124,255,41,4,75,96,207,188,221,80,196,143,108,51,218,23,202,213])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [77,83,165,84,145,44,241,189,189,116,178,122,62,239,124,255,41,4,75,96,207,188,221,80,196,143,108,51,218,23,202,213]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [77,83,165,84,145,44,241,189,189,116,178,122,62,239,124,255,41,4,75,96,207,188,221,80,196,143,108,51,218,23,202,213])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      1888#usize 1920#usize)=ok (encodeState (JGc_TX2_HashBytes.state [111,137,193,249,230,246,19,197,115,7,165,255,66,184,205,55,249,202,250,176,180,214,60,254,61,126,78,118,255,181,149,35])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 1888#usize 1920#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 1888#usize 1920#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [111,137,193,249,230,246,19,197,115,7,165,255,66,184,205,55,249,202,250,176,180,214,60,254,61,126,78,118,255,181,149,35])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 1888).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 39591).take 32)=(encodeState (JGc_TX2_HashBytes.state [111,137,193,249,230,246,19,197,115,7,165,255,66,184,205,55,249,202,250,176,180,214,60,254,61,126,78,118,255,181,149,35])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 1888#usize 1920#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [111,137,193,249,230,246,19,197,115,7,165,255,66,184,205,55,249,202,250,176,180,214,60,254,61,126,78,118,255,181,149,35])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [111,137,193,249,230,246,19,197,115,7,165,255,66,184,205,55,249,202,250,176,180,214,60,254,61,126,78,118,255,181,149,35]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [111,137,193,249,230,246,19,197,115,7,165,255,66,184,205,55,249,202,250,176,180,214,60,254,61,126,78,118,255,181,149,35])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 1600) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 1920 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 1600 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 512#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 1600 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value050) :=
    JGm_TX2_View.value (s00 s) indices00 values00 1600 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=1600#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠512#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨730#u32,JGm_TX2_View.index (s00 s) indices00 values00 1600 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s00 s).«at» 1632#usize)=ok (encodeState (JGc_TX2_HashBytes.state [125,62,11,58,152,121,161,20,87,123,59,146,157,58,136,241,164,159,33,232,66,172,208,243,124,111,180,225,182,173,183,11])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes2 0#usize 0#usize 1#usize 1632#usize 2240#usize
    512#u32 (encodeState value050) (encodeState (JGc_TX2_HashBytes.state [125,62,11,58,152,121,161,20,87,123,59,146,157,58,136,241,164,159,33,232,66,172,208,243,124,111,180,225,182,173,183,11])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read00
  simp only [show 512#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls2.source060 D hash (s00 s) 1#usize 1632#usize 512#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 1632 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 1600 v00
      512#u32 0#usize (encodeState value060) 1632#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 730#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 1632 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value051) :=
    JGm_TX2_View.value (s01 s) indices01 values01 1632 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=1632#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠730#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1152#u32,JGm_TX2_View.index (s01 s) indices01 values01 1632 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s01 s).«at» 1664#usize)=ok (encodeState (JGc_TX2_HashBytes.state [108,85,227,67,255,107,240,217,131,85,181,219,24,10,252,188,214,141,198,133,159,73,116,15,37,35,242,27,251,66,11,3])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes2 1#usize 1#usize 2#usize 1664#usize 2208#usize
    730#u32 (encodeState value051) (encodeState (JGc_TX2_HashBytes.state [108,85,227,67,255,107,240,217,131,85,181,219,24,10,252,188,214,141,198,133,159,73,116,15,37,35,242,27,251,66,11,3])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read01
  simp only [show 730#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls2.source061 D hash (s01 s) 2#usize 1664#usize 730#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 1664 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 1632 v01
      730#u32 1#usize (encodeState value061) 1664#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 1152#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 1664 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value052) :=
    JGm_TX2_View.value (s02 s) indices02 values02 1664 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=1664#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠1152#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1248#u32,JGm_TX2_View.index (s02 s) indices02 values02 1664 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s02 s).«at» 1696#usize)=ok (encodeState (JGc_TX2_HashBytes.state [20,69,131,244,4,224,142,147,45,30,160,115,55,150,86,41,62,233,146,3,5,126,120,19,244,204,58,53,181,84,196,197])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes2 2#usize 2#usize 3#usize 1696#usize 2176#usize
    1152#u32 (encodeState value052) (encodeState (JGc_TX2_HashBytes.state [20,69,131,244,4,224,142,147,45,30,160,115,55,150,86,41,62,233,146,3,5,126,120,19,244,204,58,53,181,84,196,197])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read02
  simp only [show 1152#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls2.source062 D hash (s02 s) 3#usize 1696#usize 1152#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 1696 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 1664 v02
      1152#u32 2#usize (encodeState value062) 1696#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 1248#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 1696 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value053) :=
    JGm_TX2_View.value (s03 s) indices03 values03 1696 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=1696#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠1248#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1436#u32,JGm_TX2_View.index (s03 s) indices03 values03 1696 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s03 s).«at» 1728#usize)=ok (encodeState (JGc_TX2_HashBytes.state [46,207,213,156,44,97,223,5,239,95,131,76,225,10,249,132,169,237,91,238,24,122,79,76,77,172,35,29,240,46,161,81])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes2 3#usize 3#usize 4#usize 1728#usize 2144#usize
    1248#u32 (encodeState value053) (encodeState (JGc_TX2_HashBytes.state [46,207,213,156,44,97,223,5,239,95,131,76,225,10,249,132,169,237,91,238,24,122,79,76,77,172,35,29,240,46,161,81])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read03
  simp only [show 1248#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes2 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls2.source063 D hash (s03 s) 4#usize 1728#usize 1248#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 1728 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 1696 v03
      1248#u32 3#usize (encodeState value063) 1728#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 1436#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 1728 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value054) :=
    JGm_TX2_View.value (s04 s) indices04 values04 1728 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=1728#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠1436#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1502#u32,JGm_TX2_View.index (s04 s) indices04 values04 1728 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s04 s).«at» 1760#usize)=ok (encodeState (JGc_TX2_HashBytes.state [95,12,139,86,115,166,43,216,121,70,107,251,72,70,51,33,19,180,64,129,152,241,136,194,104,235,4,19,207,59,71,38])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes2 4#usize 4#usize 5#usize 1760#usize 2112#usize
    1436#u32 (encodeState value054) (encodeState (JGc_TX2_HashBytes.state [95,12,139,86,115,166,43,216,121,70,107,251,72,70,51,33,19,180,64,129,152,241,136,194,104,235,4,19,207,59,71,38])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read04
  simp only [show 1436#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes2 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls2.source064 D hash (s04 s) 5#usize 1760#usize 1436#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 1760 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 1728 v04
      1436#u32 4#usize (encodeState value064) 1760#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 1502#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 1760 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value055) :=
    JGm_TX2_View.value (s05 s) indices05 values05 1760 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=1760#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠1502#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1508#u32,JGm_TX2_View.index (s05 s) indices05 values05 1760 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s05 s).«at» 1792#usize)=ok (encodeState (JGc_TX2_HashBytes.state [96,144,30,173,153,163,192,34,238,70,42,254,168,235,204,203,30,126,228,206,111,202,34,173,110,50,39,31,76,7,91,117])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes2 5#usize 5#usize 6#usize 1792#usize 2080#usize
    1502#u32 (encodeState value055) (encodeState (JGc_TX2_HashBytes.state [96,144,30,173,153,163,192,34,238,70,42,254,168,235,204,203,30,126,228,206,111,202,34,173,110,50,39,31,76,7,91,117])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read05
  simp only [show 1502#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes2 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls2.source065 D hash (s05 s) 6#usize 1792#usize 1502#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 1792 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 1760 v05
      1502#u32 5#usize (encodeState value065) 1792#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 1508#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 1792 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value056) :=
    JGm_TX2_View.value (s06 s) indices06 values06 1792 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=1792#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠1508#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1635#u32,JGm_TX2_View.index (s06 s) indices06 values06 1792 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s06 s).«at» 1824#usize)=ok (encodeState (JGc_TX2_HashBytes.state [193,40,69,139,235,218,184,141,95,6,104,82,149,17,63,148,181,126,57,142,185,25,231,88,16,185,114,171,2,44,236,81])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes2 6#usize 6#usize 7#usize 1824#usize 2048#usize
    1508#u32 (encodeState value056) (encodeState (JGc_TX2_HashBytes.state [193,40,69,139,235,218,184,141,95,6,104,82,149,17,63,148,181,126,57,142,185,25,231,88,16,185,114,171,2,44,236,81])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read06
  simp only [show 1508#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes2 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls2.source066 D hash (s06 s) 7#usize 1824#usize 1508#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 1824 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 1792 v06
      1508#u32 6#usize (encodeState value066) 1824#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 1635#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 1824 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value057) :=
    JGm_TX2_View.value (s07 s) indices07 values07 1824 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=1824#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠1635#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1693#u32,JGm_TX2_View.index (s07 s) indices07 values07 1824 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s07 s).«at» 1856#usize)=ok (encodeState (JGc_TX2_HashBytes.state [108,244,30,13,4,164,224,60,6,70,5,194,113,19,224,179,103,199,233,246,124,170,2,80,220,146,148,253,253,191,218,219])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes2 7#usize 7#usize 8#usize 1856#usize 2016#usize
    1635#u32 (encodeState value057) (encodeState (JGc_TX2_HashBytes.state [108,244,30,13,4,164,224,60,6,70,5,194,113,19,224,179,103,199,233,246,124,170,2,80,220,146,148,253,253,191,218,219])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read07
  simp only [show 1635#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes2 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls2.source067 D hash (s07 s) 8#usize 1856#usize 1635#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 1856 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 1824 v07
      1635#u32 7#usize (encodeState value067) 1856#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 1693#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 1856 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value058) :=
    JGm_TX2_View.value (s08 s) indices08 values08 1856 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=1856#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠1693#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1921#u32,JGm_TX2_View.index (s08 s) indices08 values08 1856 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s08 s).«at» 1888#usize)=ok (encodeState (JGc_TX2_HashBytes.state [77,83,165,84,145,44,241,189,189,116,178,122,62,239,124,255,41,4,75,96,207,188,221,80,196,143,108,51,218,23,202,213])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes2 8#usize 8#usize 9#usize 1888#usize 1984#usize
    1693#u32 (encodeState value058) (encodeState (JGc_TX2_HashBytes.state [77,83,165,84,145,44,241,189,189,116,178,122,62,239,124,255,41,4,75,96,207,188,221,80,196,143,108,51,218,23,202,213])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read08
  simp only [show 1693#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes2 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls2.source068 D hash (s08 s) 9#usize 1888#usize 1693#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 1888 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 1856 v08
      1693#u32 8#usize (encodeState value068) 1888#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 1921#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 1888 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value059) :=
    JGm_TX2_View.value (s09 s) indices09 values09 1888 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=1888#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠1921#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s09 s).«at» 1920#usize)=ok (encodeState (JGc_TX2_HashBytes.state [111,137,193,249,230,246,19,197,115,7,165,255,66,184,205,55,249,202,250,176,180,214,60,254,61,126,78,118,255,181,149,35])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes2 9#usize 9#usize 10#usize 1920#usize 1952#usize
    1921#u32 (encodeState value059) (encodeState (JGc_TX2_HashBytes.state [111,137,193,249,230,246,19,197,115,7,165,255,66,184,205,55,249,202,250,176,180,214,60,254,61,126,78,118,255,181,149,35])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read09
  simp only [show 1921#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes2 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls2.source069 D hash (s09 s) 10#usize 1920#usize 1921#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 1920 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 1888 v09
      1921#u32 9#usize (encodeState value069) 1920#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes2 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes2 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes2 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes2 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes2 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes2 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes2 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes2 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes2 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 1920
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level2_05
end

end
