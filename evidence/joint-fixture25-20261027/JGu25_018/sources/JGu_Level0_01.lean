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
namespace AspisR1.JGu_Level0_01
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGr_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGu_Supplied.nodes0
def indices00 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
def values00 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 32796#u32 0#usize (encodeState value020) 352#usize
 def indices01 : List U32 := [16398#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value020,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 46749#u32 1#usize (encodeState value021) 384#usize
 def indices02 : List U32 := [16398#u32,23374#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 73764#u32 2#usize (encodeState value022) 416#usize
 def indices03 : List U32 := [16398#u32,23374#u32,36882#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 79906#u32 3#usize (encodeState value023) 448#usize
 def indices04 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 91929#u32 4#usize (encodeState value024) 480#usize
 def indices05 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 96158#u32 5#usize (encodeState value025) 512#usize
 def indices06 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 96546#u32 6#usize (encodeState value026) 544#usize
 def indices07 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,104685#u32,108411#u32,122949#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value017,encodeState value018,encodeState value019]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 104685#u32 7#usize (encodeState value027) 576#usize
 def indices08 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,108411#u32,122949#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value018,encodeState value019]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 108411#u32 8#usize (encodeState value028) 608#usize
 def indices09 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,122949#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value019]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 122949#u32 9#usize (encodeState value029) 640#usize
 def indices10 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      320#usize 352#usize)=ok (encodeState (JGc_TX2_HashBytes.state [129,145,123,71,112,75,255,207,218,182,51,10,70,248,80,186,22,215,227,161,95,73,153,136,175,88,40,150,245,11,93,135])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 320#usize 352#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 320#usize 352#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [129,145,123,71,112,75,255,207,218,182,51,10,70,248,80,186,22,215,227,161,95,73,153,136,175,88,40,150,245,11,93,135])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 320).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 28679).take 32)=(encodeState (JGc_TX2_HashBytes.state [129,145,123,71,112,75,255,207,218,182,51,10,70,248,80,186,22,215,227,161,95,73,153,136,175,88,40,150,245,11,93,135])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 320#usize 352#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [129,145,123,71,112,75,255,207,218,182,51,10,70,248,80,186,22,215,227,161,95,73,153,136,175,88,40,150,245,11,93,135])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [129,145,123,71,112,75,255,207,218,182,51,10,70,248,80,186,22,215,227,161,95,73,153,136,175,88,40,150,245,11,93,135]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [129,145,123,71,112,75,255,207,218,182,51,10,70,248,80,186,22,215,227,161,95,73,153,136,175,88,40,150,245,11,93,135])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      352#usize 384#usize)=ok (encodeState (JGc_TX2_HashBytes.state [6,77,240,190,14,215,62,129,49,91,41,245,106,187,182,190,199,41,143,109,39,181,18,239,169,207,77,190,62,185,232,101])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 352#usize 384#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 352#usize 384#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [6,77,240,190,14,215,62,129,49,91,41,245,106,187,182,190,199,41,143,109,39,181,18,239,169,207,77,190,62,185,232,101])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 352).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 28711).take 32)=(encodeState (JGc_TX2_HashBytes.state [6,77,240,190,14,215,62,129,49,91,41,245,106,187,182,190,199,41,143,109,39,181,18,239,169,207,77,190,62,185,232,101])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 352#usize 384#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [6,77,240,190,14,215,62,129,49,91,41,245,106,187,182,190,199,41,143,109,39,181,18,239,169,207,77,190,62,185,232,101])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [6,77,240,190,14,215,62,129,49,91,41,245,106,187,182,190,199,41,143,109,39,181,18,239,169,207,77,190,62,185,232,101]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [6,77,240,190,14,215,62,129,49,91,41,245,106,187,182,190,199,41,143,109,39,181,18,239,169,207,77,190,62,185,232,101])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      384#usize 416#usize)=ok (encodeState (JGc_TX2_HashBytes.state [171,86,16,208,136,220,221,143,53,10,68,139,211,174,170,254,152,13,118,166,208,178,197,65,145,118,216,18,233,52,60,82])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 384#usize 416#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 384#usize 416#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [171,86,16,208,136,220,221,143,53,10,68,139,211,174,170,254,152,13,118,166,208,178,197,65,145,118,216,18,233,52,60,82])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 384).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 28743).take 32)=(encodeState (JGc_TX2_HashBytes.state [171,86,16,208,136,220,221,143,53,10,68,139,211,174,170,254,152,13,118,166,208,178,197,65,145,118,216,18,233,52,60,82])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 384#usize 416#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [171,86,16,208,136,220,221,143,53,10,68,139,211,174,170,254,152,13,118,166,208,178,197,65,145,118,216,18,233,52,60,82])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [171,86,16,208,136,220,221,143,53,10,68,139,211,174,170,254,152,13,118,166,208,178,197,65,145,118,216,18,233,52,60,82]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [171,86,16,208,136,220,221,143,53,10,68,139,211,174,170,254,152,13,118,166,208,178,197,65,145,118,216,18,233,52,60,82])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      416#usize 448#usize)=ok (encodeState (JGc_TX2_HashBytes.state [248,126,21,210,211,142,137,180,125,82,222,125,142,123,90,165,35,12,113,99,134,20,208,119,121,59,66,164,58,120,127,115])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 416#usize 448#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 416#usize 448#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [248,126,21,210,211,142,137,180,125,82,222,125,142,123,90,165,35,12,113,99,134,20,208,119,121,59,66,164,58,120,127,115])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 416).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 28775).take 32)=(encodeState (JGc_TX2_HashBytes.state [248,126,21,210,211,142,137,180,125,82,222,125,142,123,90,165,35,12,113,99,134,20,208,119,121,59,66,164,58,120,127,115])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 416#usize 448#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [248,126,21,210,211,142,137,180,125,82,222,125,142,123,90,165,35,12,113,99,134,20,208,119,121,59,66,164,58,120,127,115])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [248,126,21,210,211,142,137,180,125,82,222,125,142,123,90,165,35,12,113,99,134,20,208,119,121,59,66,164,58,120,127,115]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [248,126,21,210,211,142,137,180,125,82,222,125,142,123,90,165,35,12,113,99,134,20,208,119,121,59,66,164,58,120,127,115])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      448#usize 480#usize)=ok (encodeState (JGc_TX2_HashBytes.state [20,10,255,79,9,214,152,90,126,242,155,160,41,116,223,232,3,49,161,115,34,79,44,109,72,141,100,126,207,51,141,176])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 448#usize 480#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 448#usize 480#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [20,10,255,79,9,214,152,90,126,242,155,160,41,116,223,232,3,49,161,115,34,79,44,109,72,141,100,126,207,51,141,176])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 448).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 28807).take 32)=(encodeState (JGc_TX2_HashBytes.state [20,10,255,79,9,214,152,90,126,242,155,160,41,116,223,232,3,49,161,115,34,79,44,109,72,141,100,126,207,51,141,176])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 448#usize 480#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [20,10,255,79,9,214,152,90,126,242,155,160,41,116,223,232,3,49,161,115,34,79,44,109,72,141,100,126,207,51,141,176])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [20,10,255,79,9,214,152,90,126,242,155,160,41,116,223,232,3,49,161,115,34,79,44,109,72,141,100,126,207,51,141,176]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [20,10,255,79,9,214,152,90,126,242,155,160,41,116,223,232,3,49,161,115,34,79,44,109,72,141,100,126,207,51,141,176])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      480#usize 512#usize)=ok (encodeState (JGc_TX2_HashBytes.state [6,1,204,64,31,38,61,84,24,165,208,174,223,189,74,4,143,235,84,186,217,122,203,71,143,71,240,110,239,79,13,27])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 480#usize 512#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 480#usize 512#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [6,1,204,64,31,38,61,84,24,165,208,174,223,189,74,4,143,235,84,186,217,122,203,71,143,71,240,110,239,79,13,27])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 480).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 28839).take 32)=(encodeState (JGc_TX2_HashBytes.state [6,1,204,64,31,38,61,84,24,165,208,174,223,189,74,4,143,235,84,186,217,122,203,71,143,71,240,110,239,79,13,27])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 480#usize 512#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [6,1,204,64,31,38,61,84,24,165,208,174,223,189,74,4,143,235,84,186,217,122,203,71,143,71,240,110,239,79,13,27])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [6,1,204,64,31,38,61,84,24,165,208,174,223,189,74,4,143,235,84,186,217,122,203,71,143,71,240,110,239,79,13,27]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [6,1,204,64,31,38,61,84,24,165,208,174,223,189,74,4,143,235,84,186,217,122,203,71,143,71,240,110,239,79,13,27])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      512#usize 544#usize)=ok (encodeState (JGc_TX2_HashBytes.state [111,19,141,1,38,225,65,248,212,38,27,65,9,175,117,232,105,8,170,194,129,33,180,80,1,242,239,11,227,222,81,248])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 512#usize 544#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 512#usize 544#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [111,19,141,1,38,225,65,248,212,38,27,65,9,175,117,232,105,8,170,194,129,33,180,80,1,242,239,11,227,222,81,248])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 512).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 28871).take 32)=(encodeState (JGc_TX2_HashBytes.state [111,19,141,1,38,225,65,248,212,38,27,65,9,175,117,232,105,8,170,194,129,33,180,80,1,242,239,11,227,222,81,248])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 512#usize 544#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [111,19,141,1,38,225,65,248,212,38,27,65,9,175,117,232,105,8,170,194,129,33,180,80,1,242,239,11,227,222,81,248])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [111,19,141,1,38,225,65,248,212,38,27,65,9,175,117,232,105,8,170,194,129,33,180,80,1,242,239,11,227,222,81,248]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [111,19,141,1,38,225,65,248,212,38,27,65,9,175,117,232,105,8,170,194,129,33,180,80,1,242,239,11,227,222,81,248])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      544#usize 576#usize)=ok (encodeState (JGc_TX2_HashBytes.state [17,75,22,191,103,116,8,247,251,193,12,81,68,91,193,167,193,237,72,81,121,112,92,183,215,119,32,4,8,7,113,34])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 544#usize 576#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 544#usize 576#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [17,75,22,191,103,116,8,247,251,193,12,81,68,91,193,167,193,237,72,81,121,112,92,183,215,119,32,4,8,7,113,34])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 544).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 28903).take 32)=(encodeState (JGc_TX2_HashBytes.state [17,75,22,191,103,116,8,247,251,193,12,81,68,91,193,167,193,237,72,81,121,112,92,183,215,119,32,4,8,7,113,34])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 544#usize 576#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [17,75,22,191,103,116,8,247,251,193,12,81,68,91,193,167,193,237,72,81,121,112,92,183,215,119,32,4,8,7,113,34])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [17,75,22,191,103,116,8,247,251,193,12,81,68,91,193,167,193,237,72,81,121,112,92,183,215,119,32,4,8,7,113,34]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [17,75,22,191,103,116,8,247,251,193,12,81,68,91,193,167,193,237,72,81,121,112,92,183,215,119,32,4,8,7,113,34])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      576#usize 608#usize)=ok (encodeState (JGc_TX2_HashBytes.state [198,203,234,73,173,119,179,225,134,57,111,62,249,250,244,3,81,81,144,231,109,135,167,231,203,175,0,17,199,209,221,204])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 576#usize 608#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 576#usize 608#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [198,203,234,73,173,119,179,225,134,57,111,62,249,250,244,3,81,81,144,231,109,135,167,231,203,175,0,17,199,209,221,204])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 576).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 28935).take 32)=(encodeState (JGc_TX2_HashBytes.state [198,203,234,73,173,119,179,225,134,57,111,62,249,250,244,3,81,81,144,231,109,135,167,231,203,175,0,17,199,209,221,204])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 576#usize 608#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [198,203,234,73,173,119,179,225,134,57,111,62,249,250,244,3,81,81,144,231,109,135,167,231,203,175,0,17,199,209,221,204])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [198,203,234,73,173,119,179,225,134,57,111,62,249,250,244,3,81,81,144,231,109,135,167,231,203,175,0,17,199,209,221,204]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [198,203,234,73,173,119,179,225,134,57,111,62,249,250,244,3,81,81,144,231,109,135,167,231,203,175,0,17,199,209,221,204])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      608#usize 640#usize)=ok (encodeState (JGc_TX2_HashBytes.state [250,169,77,120,228,7,6,220,115,87,209,195,16,51,10,191,223,81,107,87,210,1,161,60,20,21,81,135,25,24,132,100])) := by
  unfold JGu_Supplied.nodes0
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 608#usize 640#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot0.value 608#usize 640#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [250,169,77,120,228,7,6,220,115,87,209,195,16,51,10,191,223,81,107,87,210,1,161,60,20,21,81,135,25,24,132,100])).val := by
    change (((JFw_Frames.window 28359 4672).val.drop 608).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 28967).take 32)=(encodeState (JGc_TX2_HashBytes.state [250,169,77,120,228,7,6,220,115,87,209,195,16,51,10,191,223,81,107,87,210,1,161,60,20,21,81,135,25,24,132,100])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot0.value 608#usize 640#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [250,169,77,120,228,7,6,220,115,87,209,195,16,51,10,191,223,81,107,87,210,1,161,60,20,21,81,135,25,24,132,100])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [250,169,77,120,228,7,6,220,115,87,209,195,16,51,10,191,223,81,107,87,210,1,161,60,20,21,81,135,25,24,132,100]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [250,169,77,120,228,7,6,220,115,87,209,195,16,51,10,191,223,81,107,87,210,1,161,60,20,21,81,135,25,24,132,100])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 320) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGu_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 640 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 320 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 32796#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 320 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value010) :=
    JGm_TX2_View.value (s00 s) indices00 values00 320 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=320#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠32796#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨46749#u32,JGm_TX2_View.index (s00 s) indices00 values00 320 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s00 s).«at» 352#usize)=ok (encodeState (JGc_TX2_HashBytes.state [129,145,123,71,112,75,255,207,218,182,51,10,70,248,80,186,22,215,227,161,95,73,153,136,175,88,40,150,245,11,93,135])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGu_Supplied.nodes0 0#usize 0#usize 1#usize 352#usize 4096#usize
    32796#u32 (encodeState value010) (encodeState (JGc_TX2_HashBytes.state [129,145,123,71,112,75,255,207,218,182,51,10,70,248,80,186,22,215,227,161,95,73,153,136,175,88,40,150,245,11,93,135])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGu_Supplied.length0];decide) read00
  simp only [show 32796#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGu_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGu_ParentCalls0.source020 D hash (s00 s) 1#usize 352#usize 32796#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 352 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 320 v00
      32796#u32 0#usize (encodeState value020) 352#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 46749#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 352 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value011) :=
    JGm_TX2_View.value (s01 s) indices01 values01 352 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=352#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠46749#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨73764#u32,JGm_TX2_View.index (s01 s) indices01 values01 352 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s01 s).«at» 384#usize)=ok (encodeState (JGc_TX2_HashBytes.state [6,77,240,190,14,215,62,129,49,91,41,245,106,187,182,190,199,41,143,109,39,181,18,239,169,207,77,190,62,185,232,101])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGu_Supplied.nodes0 1#usize 1#usize 2#usize 384#usize 4064#usize
    46749#u32 (encodeState value011) (encodeState (JGc_TX2_HashBytes.state [6,77,240,190,14,215,62,129,49,91,41,245,106,187,182,190,199,41,143,109,39,181,18,239,169,207,77,190,62,185,232,101])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGu_Supplied.length0];decide) read01
  simp only [show 46749#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGu_Supplied.nodes0 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGu_ParentCalls0.source021 D hash (s01 s) 2#usize 384#usize 46749#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 384 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 352 v01
      46749#u32 1#usize (encodeState value021) 384#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 73764#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 384 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value012) :=
    JGm_TX2_View.value (s02 s) indices02 values02 384 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=384#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠73764#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨79906#u32,JGm_TX2_View.index (s02 s) indices02 values02 384 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s02 s).«at» 416#usize)=ok (encodeState (JGc_TX2_HashBytes.state [171,86,16,208,136,220,221,143,53,10,68,139,211,174,170,254,152,13,118,166,208,178,197,65,145,118,216,18,233,52,60,82])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGu_Supplied.nodes0 2#usize 2#usize 3#usize 416#usize 4032#usize
    73764#u32 (encodeState value012) (encodeState (JGc_TX2_HashBytes.state [171,86,16,208,136,220,221,143,53,10,68,139,211,174,170,254,152,13,118,166,208,178,197,65,145,118,216,18,233,52,60,82])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGu_Supplied.length0];decide) read02
  simp only [show 73764#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGu_Supplied.nodes0 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGu_ParentCalls0.source022 D hash (s02 s) 3#usize 416#usize 73764#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 416 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 384 v02
      73764#u32 2#usize (encodeState value022) 416#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 79906#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 416 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value013) :=
    JGm_TX2_View.value (s03 s) indices03 values03 416 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=416#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠79906#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨91929#u32,JGm_TX2_View.index (s03 s) indices03 values03 416 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s03 s).«at» 448#usize)=ok (encodeState (JGc_TX2_HashBytes.state [248,126,21,210,211,142,137,180,125,82,222,125,142,123,90,165,35,12,113,99,134,20,208,119,121,59,66,164,58,120,127,115])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGu_Supplied.nodes0 3#usize 3#usize 4#usize 448#usize 4000#usize
    79906#u32 (encodeState value013) (encodeState (JGc_TX2_HashBytes.state [248,126,21,210,211,142,137,180,125,82,222,125,142,123,90,165,35,12,113,99,134,20,208,119,121,59,66,164,58,120,127,115])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGu_Supplied.length0];decide) read03
  simp only [show 79906#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGu_Supplied.nodes0 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGu_ParentCalls0.source023 D hash (s03 s) 4#usize 448#usize 79906#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 448 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 416 v03
      79906#u32 3#usize (encodeState value023) 448#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 91929#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 448 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value014) :=
    JGm_TX2_View.value (s04 s) indices04 values04 448 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=448#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠91929#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨96158#u32,JGm_TX2_View.index (s04 s) indices04 values04 448 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s04 s).«at» 480#usize)=ok (encodeState (JGc_TX2_HashBytes.state [20,10,255,79,9,214,152,90,126,242,155,160,41,116,223,232,3,49,161,115,34,79,44,109,72,141,100,126,207,51,141,176])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGu_Supplied.nodes0 4#usize 4#usize 5#usize 480#usize 3968#usize
    91929#u32 (encodeState value014) (encodeState (JGc_TX2_HashBytes.state [20,10,255,79,9,214,152,90,126,242,155,160,41,116,223,232,3,49,161,115,34,79,44,109,72,141,100,126,207,51,141,176])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGu_Supplied.length0];decide) read04
  simp only [show 91929#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGu_Supplied.nodes0 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGu_ParentCalls0.source024 D hash (s04 s) 5#usize 480#usize 91929#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 480 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 448 v04
      91929#u32 4#usize (encodeState value024) 480#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 96158#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 480 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value015) :=
    JGm_TX2_View.value (s05 s) indices05 values05 480 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=480#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠96158#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨96546#u32,JGm_TX2_View.index (s05 s) indices05 values05 480 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s05 s).«at» 512#usize)=ok (encodeState (JGc_TX2_HashBytes.state [6,1,204,64,31,38,61,84,24,165,208,174,223,189,74,4,143,235,84,186,217,122,203,71,143,71,240,110,239,79,13,27])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGu_Supplied.nodes0 5#usize 5#usize 6#usize 512#usize 3936#usize
    96158#u32 (encodeState value015) (encodeState (JGc_TX2_HashBytes.state [6,1,204,64,31,38,61,84,24,165,208,174,223,189,74,4,143,235,84,186,217,122,203,71,143,71,240,110,239,79,13,27])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGu_Supplied.length0];decide) read05
  simp only [show 96158#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGu_Supplied.nodes0 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGu_ParentCalls0.source025 D hash (s05 s) 6#usize 512#usize 96158#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 512 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 480 v05
      96158#u32 5#usize (encodeState value025) 512#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 96546#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 512 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value016) :=
    JGm_TX2_View.value (s06 s) indices06 values06 512 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=512#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠96546#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨104685#u32,JGm_TX2_View.index (s06 s) indices06 values06 512 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s06 s).«at» 544#usize)=ok (encodeState (JGc_TX2_HashBytes.state [111,19,141,1,38,225,65,248,212,38,27,65,9,175,117,232,105,8,170,194,129,33,180,80,1,242,239,11,227,222,81,248])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGu_Supplied.nodes0 6#usize 6#usize 7#usize 544#usize 3904#usize
    96546#u32 (encodeState value016) (encodeState (JGc_TX2_HashBytes.state [111,19,141,1,38,225,65,248,212,38,27,65,9,175,117,232,105,8,170,194,129,33,180,80,1,242,239,11,227,222,81,248])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGu_Supplied.length0];decide) read06
  simp only [show 96546#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGu_Supplied.nodes0 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGu_ParentCalls0.source026 D hash (s06 s) 7#usize 544#usize 96546#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 544 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 512 v06
      96546#u32 6#usize (encodeState value026) 544#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 104685#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 544 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value017) :=
    JGm_TX2_View.value (s07 s) indices07 values07 544 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=544#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠104685#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨108411#u32,JGm_TX2_View.index (s07 s) indices07 values07 544 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s07 s).«at» 576#usize)=ok (encodeState (JGc_TX2_HashBytes.state [17,75,22,191,103,116,8,247,251,193,12,81,68,91,193,167,193,237,72,81,121,112,92,183,215,119,32,4,8,7,113,34])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGu_Supplied.nodes0 7#usize 7#usize 8#usize 576#usize 3872#usize
    104685#u32 (encodeState value017) (encodeState (JGc_TX2_HashBytes.state [17,75,22,191,103,116,8,247,251,193,12,81,68,91,193,167,193,237,72,81,121,112,92,183,215,119,32,4,8,7,113,34])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGu_Supplied.length0];decide) read07
  simp only [show 104685#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGu_Supplied.nodes0 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGu_ParentCalls0.source027 D hash (s07 s) 8#usize 576#usize 104685#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 576 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 544 v07
      104685#u32 7#usize (encodeState value027) 576#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 108411#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 576 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value018) :=
    JGm_TX2_View.value (s08 s) indices08 values08 576 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=576#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠108411#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨122949#u32,JGm_TX2_View.index (s08 s) indices08 values08 576 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s08 s).«at» 608#usize)=ok (encodeState (JGc_TX2_HashBytes.state [198,203,234,73,173,119,179,225,134,57,111,62,249,250,244,3,81,81,144,231,109,135,167,231,203,175,0,17,199,209,221,204])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGu_Supplied.nodes0 8#usize 8#usize 9#usize 608#usize 3840#usize
    108411#u32 (encodeState value018) (encodeState (JGc_TX2_HashBytes.state [198,203,234,73,173,119,179,225,134,57,111,62,249,250,244,3,81,81,144,231,109,135,167,231,203,175,0,17,199,209,221,204])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGu_Supplied.length0];decide) read08
  simp only [show 108411#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGu_Supplied.nodes0 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGu_ParentCalls0.source028 D hash (s08 s) 9#usize 608#usize 108411#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 608 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 576 v08
      108411#u32 8#usize (encodeState value028) 608#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 122949#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 608 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value019) :=
    JGm_TX2_View.value (s09 s) indices09 values09 608 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=608#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠122949#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s09 s).«at» 640#usize)=ok (encodeState (JGc_TX2_HashBytes.state [250,169,77,120,228,7,6,220,115,87,209,195,16,51,10,191,223,81,107,87,210,1,161,60,20,21,81,135,25,24,132,100])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGu_Supplied.nodes0 9#usize 9#usize 10#usize 640#usize 3808#usize
    122949#u32 (encodeState value019) (encodeState (JGc_TX2_HashBytes.state [250,169,77,120,228,7,6,220,115,87,209,195,16,51,10,191,223,81,107,87,210,1,161,60,20,21,81,135,25,24,132,100])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGu_Supplied.length0];decide) read09
  simp only [show 122949#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGu_Supplied.nodes0 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGu_ParentCalls0.source029 D hash (s09 s) 10#usize 640#usize 122949#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 640 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 608 v09
      122949#u32 9#usize (encodeState value029) 640#usize (by decide)
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
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGu_Supplied.nodes0 6#usize 6#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGu_Supplied.nodes0 7#usize 7#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGu_Supplied.nodes0 8#usize 8#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGu_Supplied.nodes0 9#usize 9#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGu_Supplied.nodes0 10#usize 10#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 640
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JGu_Level0_01
end
