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
namespace AspisR1.JGu_Level2_10
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGu_Supplied.nodes2
def indices00 : List U32 := [16#u32,22#u32,36#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
def values00 : List (Array U8 32#usize) := [encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 16#u32 0#usize (encodeState value110) 3232#usize
 def indices01 : List U32 := [8#u32,22#u32,36#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value110,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 22#u32 1#usize (encodeState value111) 3264#usize
 def indices02 : List U32 := [8#u32,11#u32,36#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 36#u32 2#usize (encodeState value112) 3296#usize
 def indices03 : List U32 := [8#u32,11#u32,18#u32,39#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 39#u32 3#usize (encodeState value113) 3328#usize
 def indices04 : List U32 := [8#u32,11#u32,18#u32,19#u32,44#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value104,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 44#u32 4#usize (encodeState value114) 3360#usize
 def indices05 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,46#u32,47#u32,51#u32,52#u32,60#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value105,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 46#u32 5#usize (encodeState value115) 3360#usize
 def indices06 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,47#u32,51#u32,52#u32,60#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value106,encodeState value107,encodeState value108,encodeState value109]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 51#u32 6#usize (encodeState value116) 3392#usize
 def indices07 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,51#u32,52#u32,60#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value107,encodeState value108,encodeState value109]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 52#u32 7#usize (encodeState value117) 3424#usize
 def indices08 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,52#u32,60#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value108,encodeState value109]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 60#u32 8#usize (encodeState value118) 3456#usize
 def indices09 : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32,60#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value109]
def output (s : reference.Scratch) : reference.Scratch := {s09 s with n:=9#usize}
 def indicesOut : List U32 := [8#u32,11#u32,18#u32,19#u32,22#u32,23#u32,25#u32,26#u32,30#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      3200#usize 3232#usize)=ok (encodeState (JGc_TX2_HashBytes.state [59,119,73,169,22,234,180,231,182,173,95,170,28,240,254,211,36,169,197,26,155,126,34,120,70,14,2,233,116,165,77,238])) := by
  unfold JGu_Supplied.nodes2
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3200#usize 3232#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3200#usize 3232#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [59,119,73,169,22,234,180,231,182,173,95,170,28,240,254,211,36,169,197,26,155,126,34,120,70,14,2,233,116,165,77,238])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3200).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 40903).take 32)=(encodeState (JGc_TX2_HashBytes.state [59,119,73,169,22,234,180,231,182,173,95,170,28,240,254,211,36,169,197,26,155,126,34,120,70,14,2,233,116,165,77,238])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3200#usize 3232#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [59,119,73,169,22,234,180,231,182,173,95,170,28,240,254,211,36,169,197,26,155,126,34,120,70,14,2,233,116,165,77,238])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [59,119,73,169,22,234,180,231,182,173,95,170,28,240,254,211,36,169,197,26,155,126,34,120,70,14,2,233,116,165,77,238]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [59,119,73,169,22,234,180,231,182,173,95,170,28,240,254,211,36,169,197,26,155,126,34,120,70,14,2,233,116,165,77,238])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      3232#usize 3264#usize)=ok (encodeState (JGc_TX2_HashBytes.state [155,115,130,156,18,114,181,14,247,172,123,90,64,80,209,183,141,7,129,131,179,236,78,203,48,11,88,165,65,162,198,183])) := by
  unfold JGu_Supplied.nodes2
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3232#usize 3264#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3232#usize 3264#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [155,115,130,156,18,114,181,14,247,172,123,90,64,80,209,183,141,7,129,131,179,236,78,203,48,11,88,165,65,162,198,183])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3232).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 40935).take 32)=(encodeState (JGc_TX2_HashBytes.state [155,115,130,156,18,114,181,14,247,172,123,90,64,80,209,183,141,7,129,131,179,236,78,203,48,11,88,165,65,162,198,183])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3232#usize 3264#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [155,115,130,156,18,114,181,14,247,172,123,90,64,80,209,183,141,7,129,131,179,236,78,203,48,11,88,165,65,162,198,183])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [155,115,130,156,18,114,181,14,247,172,123,90,64,80,209,183,141,7,129,131,179,236,78,203,48,11,88,165,65,162,198,183]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [155,115,130,156,18,114,181,14,247,172,123,90,64,80,209,183,141,7,129,131,179,236,78,203,48,11,88,165,65,162,198,183])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      3264#usize 3296#usize)=ok (encodeState (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26])) := by
  unfold JGu_Supplied.nodes2
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3264#usize 3296#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3264#usize 3296#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3264).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 40967).take 32)=(encodeState (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3264#usize 3296#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      3296#usize 3328#usize)=ok (encodeState (JGc_TX2_HashBytes.state [21,19,134,173,7,2,210,241,42,75,194,167,15,45,14,161,26,153,154,65,84,193,25,180,34,59,39,191,21,32,25,135])) := by
  unfold JGu_Supplied.nodes2
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3296#usize 3328#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3296#usize 3328#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [21,19,134,173,7,2,210,241,42,75,194,167,15,45,14,161,26,153,154,65,84,193,25,180,34,59,39,191,21,32,25,135])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3296).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 40999).take 32)=(encodeState (JGc_TX2_HashBytes.state [21,19,134,173,7,2,210,241,42,75,194,167,15,45,14,161,26,153,154,65,84,193,25,180,34,59,39,191,21,32,25,135])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3296#usize 3328#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [21,19,134,173,7,2,210,241,42,75,194,167,15,45,14,161,26,153,154,65,84,193,25,180,34,59,39,191,21,32,25,135])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [21,19,134,173,7,2,210,241,42,75,194,167,15,45,14,161,26,153,154,65,84,193,25,180,34,59,39,191,21,32,25,135]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [21,19,134,173,7,2,210,241,42,75,194,167,15,45,14,161,26,153,154,65,84,193,25,180,34,59,39,191,21,32,25,135])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      3328#usize 3360#usize)=ok (encodeState (JGc_TX2_HashBytes.state [186,104,47,209,122,14,221,153,173,57,67,129,86,66,66,233,32,56,115,230,42,38,98,22,111,235,154,246,230,200,89,9])) := by
  unfold JGu_Supplied.nodes2
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3328#usize 3360#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3328#usize 3360#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [186,104,47,209,122,14,221,153,173,57,67,129,86,66,66,233,32,56,115,230,42,38,98,22,111,235,154,246,230,200,89,9])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3328).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41031).take 32)=(encodeState (JGc_TX2_HashBytes.state [186,104,47,209,122,14,221,153,173,57,67,129,86,66,66,233,32,56,115,230,42,38,98,22,111,235,154,246,230,200,89,9])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3328#usize 3360#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [186,104,47,209,122,14,221,153,173,57,67,129,86,66,66,233,32,56,115,230,42,38,98,22,111,235,154,246,230,200,89,9])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [186,104,47,209,122,14,221,153,173,57,67,129,86,66,66,233,32,56,115,230,42,38,98,22,111,235,154,246,230,200,89,9]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [186,104,47,209,122,14,221,153,173,57,67,129,86,66,66,233,32,56,115,230,42,38,98,22,111,235,154,246,230,200,89,9])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      3360#usize 3392#usize)=ok (encodeState (JGc_TX2_HashBytes.state [160,11,21,231,220,161,4,194,145,32,85,167,167,102,254,212,177,251,97,177,99,36,215,15,114,51,84,17,30,107,226,151])) := by
  unfold JGu_Supplied.nodes2
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3360#usize 3392#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3360#usize 3392#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [160,11,21,231,220,161,4,194,145,32,85,167,167,102,254,212,177,251,97,177,99,36,215,15,114,51,84,17,30,107,226,151])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3360).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41063).take 32)=(encodeState (JGc_TX2_HashBytes.state [160,11,21,231,220,161,4,194,145,32,85,167,167,102,254,212,177,251,97,177,99,36,215,15,114,51,84,17,30,107,226,151])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3360#usize 3392#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [160,11,21,231,220,161,4,194,145,32,85,167,167,102,254,212,177,251,97,177,99,36,215,15,114,51,84,17,30,107,226,151])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [160,11,21,231,220,161,4,194,145,32,85,167,167,102,254,212,177,251,97,177,99,36,215,15,114,51,84,17,30,107,226,151]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [160,11,21,231,220,161,4,194,145,32,85,167,167,102,254,212,177,251,97,177,99,36,215,15,114,51,84,17,30,107,226,151])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      3392#usize 3424#usize)=ok (encodeState (JGc_TX2_HashBytes.state [79,82,178,84,61,147,76,0,223,43,6,169,212,57,122,92,55,118,68,198,170,121,50,188,215,151,199,101,127,208,161,110])) := by
  unfold JGu_Supplied.nodes2
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3392#usize 3424#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3392#usize 3424#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [79,82,178,84,61,147,76,0,223,43,6,169,212,57,122,92,55,118,68,198,170,121,50,188,215,151,199,101,127,208,161,110])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3392).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41095).take 32)=(encodeState (JGc_TX2_HashBytes.state [79,82,178,84,61,147,76,0,223,43,6,169,212,57,122,92,55,118,68,198,170,121,50,188,215,151,199,101,127,208,161,110])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3392#usize 3424#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [79,82,178,84,61,147,76,0,223,43,6,169,212,57,122,92,55,118,68,198,170,121,50,188,215,151,199,101,127,208,161,110])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [79,82,178,84,61,147,76,0,223,43,6,169,212,57,122,92,55,118,68,198,170,121,50,188,215,151,199,101,127,208,161,110]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [79,82,178,84,61,147,76,0,223,43,6,169,212,57,122,92,55,118,68,198,170,121,50,188,215,151,199,101,127,208,161,110])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      3424#usize 3456#usize)=ok (encodeState (JGc_TX2_HashBytes.state [113,199,16,24,52,72,40,241,79,147,76,57,246,194,155,42,154,10,38,24,158,221,37,151,184,52,224,109,73,38,75,31])) := by
  unfold JGu_Supplied.nodes2
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3424#usize 3456#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 3424#usize 3456#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [113,199,16,24,52,72,40,241,79,147,76,57,246,194,155,42,154,10,38,24,158,221,37,151,184,52,224,109,73,38,75,31])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 3424).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 41127).take 32)=(encodeState (JGc_TX2_HashBytes.state [113,199,16,24,52,72,40,241,79,147,76,57,246,194,155,42,154,10,38,24,158,221,37,151,184,52,224,109,73,38,75,31])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof10.bytes,JFx_DataProof10.c00_length,JFx_DataProof10.c01_length,JFx_DataProof10.c02_length,JFx_DataProof10.c03_length,JFx_DataProof10.c04_length,JFx_DataProof10.c05_length,JFx_DataProof10.c06_length,JFx_DataProof10.c07_length,JFx_DataProof10.c08_length,JFx_DataProof10.c09_length,JFx_DataProof10.c10_length,JFx_DataProof10.c11_length,JFx_DataProof10.c12_length,JFx_DataProof10.c13_length,JFx_DataProof10.c14_length,JFx_DataProof10.c15_length,JFx_DataProof10.c16_length,JFx_DataProof10.c17_length,JFx_DataProof10.c18_length,JFx_DataProof10.c19_length,JFx_DataProof10.c20_length,JFx_DataProof10.c21_length,JFx_DataProof10.c22_length,JFx_DataProof10.c23_length,JFx_DataProof10.c24_length,JFx_DataProof10.c25_length,JFx_DataProof10.c26_length,JFx_DataProof10.c27_length,JFx_DataProof10.c28_length,JFx_DataProof10.c29_length,JFx_DataProof10.c30_length,JFx_DataProof10.c31_length,JFx_DataProof10.c32_length,JFx_DataProof10.c33_length,JFx_DataProof10.c34_length,JFx_DataProof10.c35_length,JFx_DataProof10.c36_length,JFx_DataProof10.c37_length,JFx_DataProof10.c38_length,JFx_DataProof10.c39_length,JFx_DataProof10.c40_length,JFx_DataProof10.c41_length,JFx_DataProof10.c42_length,JFx_DataProof10.c43_length,JFx_DataProof10.c44_length,JFx_DataProof10.c45_length,JFx_DataProof10.c46_length,JFx_DataProof10.c47_length,JFx_DataProof10.c48_length,JFx_DataProof10.c49_length,JFx_DataProof10.c50_length,JFx_DataProof10.c51_length,JFx_DataProof10.c52_length,JFx_DataProof10.c53_length,JFx_DataProof10.c54_length,JFx_DataProof10.c55_length,JFx_DataProof10.c56_length,JFx_DataProof10.c57_length,JFx_DataProof10.c58_length,JFx_DataProof10.c59_length,JFx_DataProof10.c60_length,JFx_DataProof10.c61_length,JFx_DataProof10.c62_length,JFx_DataProof10.c63_length,JFx_DataProof10.c64_length,JFx_DataProof10.c65_length,JFx_DataProof10.c66_length,JFx_DataProof10.c67_length,JFx_DataProof10.c68_length,JFx_DataProof10.c69_length,JFx_DataProof10.c70_length,JFx_DataProof10.c71_length,JFx_DataProof10.c72_length,JFx_DataProof10.c73_length,JFx_DataProof10.c74_length,JFx_DataProof10.c75_length,JFx_DataProof10.c76_length,JFx_DataProof10.c77_length,JFx_DataProof10.c78_length,JFx_DataProof10.c79_length,JFx_DataProof10.c80_length,JFx_DataProof10.c81_length,JFx_DataProof10.c82_length,JFx_DataProof10.c83_length,JFx_DataProof10.c84_length,JFx_DataProof10.c85_length,JFx_DataProof10.c86_length,JFx_DataProof10.c87_length,JFx_DataProof10.c88_length,JFx_DataProof10.c89_length,JFx_DataProof10.c90_length,JFx_DataProof10.c91_length,JFx_DataProof10.c92_length,JFx_DataProof10.c93_length,JFx_DataProof10.c94_length,JFx_DataProof10.c95_length,JFx_DataProof10.c96_length,JFx_DataProof10.c97_length,JFx_DataProof10.c98_length,JFx_DataProof10.c99_length,JFx_DataProof10.c100_length,JFx_DataProof10.c101_length,JFx_DataProof10.c102_length,JFx_DataProof10.c103_length,JFx_DataProof10.c104_length,JFx_DataProof10.c105_length,JFx_DataProof10.c106_length,JFx_DataProof10.c107_length,JFx_DataProof10.c108_length,JFx_DataProof10.c109_length,JFx_DataProof10.c110_length,JFx_DataProof10.c111_length,JFx_DataProof10.c112_length,JFx_DataProof10.c113_length,JFx_DataProof10.c114_length,JFx_DataProof10.c115_length,JFx_DataProof10.c116_length,JFx_DataProof10.c117_length,JFx_DataProof10.c118_length,JFx_DataProof10.c119_length,JFx_DataProof10.c120_length,JFx_DataProof10.c121_length,JFx_DataProof10.c122_length,JFx_DataProof10.c123_length,JFx_DataProof10.c124_length,JFx_DataProof10.c125_length,JFx_DataProof10.c126_length,JFx_DataProof10.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 3424#usize 3456#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [113,199,16,24,52,72,40,241,79,147,76,57,246,194,155,42,154,10,38,24,158,221,37,151,184,52,224,109,73,38,75,31])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [113,199,16,24,52,72,40,241,79,147,76,57,246,194,155,42,154,10,38,24,158,221,37,151,184,52,224,109,73,38,75,31]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [113,199,16,24,52,72,40,241,79,147,76,57,246,194,155,42,154,10,38,24,158,221,37,151,184,52,224,109,73,38,75,31])).property];decide)
  exact same ▸ run
#print axioms read08
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3200) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3456 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3200 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 16#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3200 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value100) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3200 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3200#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠16#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨22#u32,JGm_TX2_View.index (s00 s) indices00 values00 3200 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      (s00 s).«at» 3232#usize)=ok (encodeState (JGc_TX2_HashBytes.state [59,119,73,169,22,234,180,231,182,173,95,170,28,240,254,211,36,169,197,26,155,126,34,120,70,14,2,233,116,165,77,238])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGu_Supplied.nodes2 0#usize 0#usize 1#usize 3232#usize 640#usize
    16#u32 (encodeState value100) (encodeState (JGc_TX2_HashBytes.state [59,119,73,169,22,234,180,231,182,173,95,170,28,240,254,211,36,169,197,26,155,126,34,120,70,14,2,233,116,165,77,238])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGu_Supplied.length2];decide) read00
  simp only [show 16#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGu_ParentCalls2.source110 D hash (s00 s) 1#usize 3232#usize 16#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3232 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3200 v00
      16#u32 0#usize (encodeState value110) 3232#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 22#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 3232 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value101) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3232 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=3232#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠22#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨36#u32,JGm_TX2_View.index (s01 s) indices01 values01 3232 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      (s01 s).«at» 3264#usize)=ok (encodeState (JGc_TX2_HashBytes.state [155,115,130,156,18,114,181,14,247,172,123,90,64,80,209,183,141,7,129,131,179,236,78,203,48,11,88,165,65,162,198,183])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGu_Supplied.nodes2 1#usize 1#usize 2#usize 3264#usize 608#usize
    22#u32 (encodeState value101) (encodeState (JGc_TX2_HashBytes.state [155,115,130,156,18,114,181,14,247,172,123,90,64,80,209,183,141,7,129,131,179,236,78,203,48,11,88,165,65,162,198,183])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGu_Supplied.length2];decide) read01
  simp only [show 22#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGu_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGu_ParentCalls2.source111 D hash (s01 s) 2#usize 3264#usize 22#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 3264 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 3232 v01
      22#u32 1#usize (encodeState value111) 3264#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 36#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 3264 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value102) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3264 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=3264#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠36#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨39#u32,JGm_TX2_View.index (s02 s) indices02 values02 3264 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      (s02 s).«at» 3296#usize)=ok (encodeState (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGu_Supplied.nodes2 2#usize 2#usize 3#usize 3296#usize 576#usize
    36#u32 (encodeState value102) (encodeState (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGu_Supplied.length2];decide) read02
  simp only [show 36#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGu_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGu_ParentCalls2.source112 D hash (s02 s) 3#usize 3296#usize 36#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 3296 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 3264 v02
      36#u32 2#usize (encodeState value112) 3296#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 39#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 3296 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value103) :=
    JGm_TX2_View.value (s03 s) indices03 values03 3296 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=3296#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠39#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨44#u32,JGm_TX2_View.index (s03 s) indices03 values03 3296 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      (s03 s).«at» 3328#usize)=ok (encodeState (JGc_TX2_HashBytes.state [21,19,134,173,7,2,210,241,42,75,194,167,15,45,14,161,26,153,154,65,84,193,25,180,34,59,39,191,21,32,25,135])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGu_Supplied.nodes2 3#usize 3#usize 4#usize 3328#usize 544#usize
    39#u32 (encodeState value103) (encodeState (JGc_TX2_HashBytes.state [21,19,134,173,7,2,210,241,42,75,194,167,15,45,14,161,26,153,154,65,84,193,25,180,34,59,39,191,21,32,25,135])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGu_Supplied.length2];decide) read03
  simp only [show 39#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGu_Supplied.nodes2 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGu_ParentCalls2.source113 D hash (s03 s) 4#usize 3328#usize 39#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 3328 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 3296 v03
      39#u32 3#usize (encodeState value113) 3328#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 44#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 3328 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value104) :=
    JGm_TX2_View.value (s04 s) indices04 values04 3328 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=3328#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠44#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨46#u32,JGm_TX2_View.index (s04 s) indices04 values04 3328 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      (s04 s).«at» 3360#usize)=ok (encodeState (JGc_TX2_HashBytes.state [186,104,47,209,122,14,221,153,173,57,67,129,86,66,66,233,32,56,115,230,42,38,98,22,111,235,154,246,230,200,89,9])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGu_Supplied.nodes2 4#usize 4#usize 5#usize 3360#usize 512#usize
    44#u32 (encodeState value104) (encodeState (JGc_TX2_HashBytes.state [186,104,47,209,122,14,221,153,173,57,67,129,86,66,66,233,32,56,115,230,42,38,98,22,111,235,154,246,230,200,89,9])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGu_Supplied.length2];decide) read04
  simp only [show 44#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGu_Supplied.nodes2 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGu_ParentCalls2.source114 D hash (s04 s) 5#usize 3360#usize 44#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 3360 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 3328 v04
      44#u32 4#usize (encodeState value114) 3360#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 46#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 3360 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value105) :=
    JGm_TX2_View.value (s05 s) indices05 values05 3360 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=3360#usize := UScalar.eq_of_val_eq v05.at_eq
  have rn05 : Array.index_usize (s05 s).idx 6#usize=ok (46#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s05 s) indices05 values05 3360 v05 6#usize (by decide)
  have rr05 : Array.index_usize (s05 s).val 6#usize=ok (encodeState value106) :=
    JGm_TX2_View.value (s05 s) indices05 values05 3360 v05 6#usize (by decide)
  have selected05 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGu_Supplied.nodes2 5#usize 5#usize 6#usize 7#usize 46#u32
    (encodeState value105) (encodeState value106) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (6:Nat)<(s05 s).n.val;rw [v05.size];decide)
    rn05 rr05 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGu_Supplied.nodes2 5#usize 5#usize=
        ok (.Next (s06 s) 7#usize 6#usize) := by
    rw [selected05]
    rw [cursor05]
    exact JGu_ParentCalls2.source115 D hash (s05 s) 7#usize 3360#usize 46#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 3360 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 3360 v05
      46#u32 5#usize (encodeState value115) 3360#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 7#usize=ok 51#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 3360 v06 7#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 7#usize=ok (encodeState value107) :=
    JGm_TX2_View.value (s06 s) indices06 values06 3360 v06 7#usize (by decide)
  have active06 : 7#usize<(s06 s).n := by
    change (7:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=3360#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 8#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 8#usize=ok other ∧ other≠51#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨52#u32,JGm_TX2_View.index (s06 s) indices06 values06 3360 v06 8#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      (s06 s).«at» 3392#usize)=ok (encodeState (JGc_TX2_HashBytes.state [160,11,21,231,220,161,4,194,145,32,85,167,167,102,254,212,177,251,97,177,99,36,215,15,114,51,84,17,30,107,226,151])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGu_Supplied.nodes2 7#usize 6#usize 8#usize 3392#usize 480#usize
    51#u32 (encodeState value107) (encodeState (JGc_TX2_HashBytes.state [160,11,21,231,220,161,4,194,145,32,85,167,167,102,254,212,177,251,97,177,99,36,215,15,114,51,84,17,30,107,226,151])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGu_Supplied.length2];decide) read06
  simp only [show 51#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGu_Supplied.nodes2 7#usize 6#usize=
        ok (.Next (s07 s) 8#usize 7#usize) := by
    rw [selected06]
    exact JGu_ParentCalls2.source116 D hash (s06 s) 8#usize 3392#usize 51#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 3392 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 3360 v06
      51#u32 6#usize (encodeState value116) 3392#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 8#usize=ok 52#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 3392 v07 8#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 8#usize=ok (encodeState value108) :=
    JGm_TX2_View.value (s07 s) indices07 values07 3392 v07 8#usize (by decide)
  have active07 : 8#usize<(s07 s).n := by
    change (8:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=3392#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 9#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 9#usize=ok other ∧ other≠52#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨60#u32,JGm_TX2_View.index (s07 s) indices07 values07 3392 v07 9#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      (s07 s).«at» 3424#usize)=ok (encodeState (JGc_TX2_HashBytes.state [79,82,178,84,61,147,76,0,223,43,6,169,212,57,122,92,55,118,68,198,170,121,50,188,215,151,199,101,127,208,161,110])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGu_Supplied.nodes2 8#usize 7#usize 9#usize 3424#usize 448#usize
    52#u32 (encodeState value108) (encodeState (JGc_TX2_HashBytes.state [79,82,178,84,61,147,76,0,223,43,6,169,212,57,122,92,55,118,68,198,170,121,50,188,215,151,199,101,127,208,161,110])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGu_Supplied.length2];decide) read07
  simp only [show 52#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGu_Supplied.nodes2 8#usize 7#usize=
        ok (.Next (s08 s) 9#usize 8#usize) := by
    rw [selected07]
    exact JGu_ParentCalls2.source117 D hash (s07 s) 9#usize 3424#usize 52#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 3424 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 3392 v07
      52#u32 7#usize (encodeState value117) 3424#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 9#usize=ok 60#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 3424 v08 9#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 9#usize=ok (encodeState value109) :=
    JGm_TX2_View.value (s08 s) indices08 values08 3424 v08 9#usize (by decide)
  have active08 : 9#usize<(s08 s).n := by
    change (9:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=3424#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 10#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 10#usize=ok other ∧ other≠60#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s08 s).n.val at more
    rw [v08.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read08 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      (s08 s).«at» 3456#usize)=ok (encodeState (JGc_TX2_HashBytes.state [113,199,16,24,52,72,40,241,79,147,76,57,246,194,155,42,154,10,38,24,158,221,37,151,184,52,224,109,73,38,75,31])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGu_Supplied.nodes2 9#usize 8#usize 10#usize 3456#usize 416#usize
    60#u32 (encodeState value109) (encodeState (JGc_TX2_HashBytes.state [113,199,16,24,52,72,40,241,79,147,76,57,246,194,155,42,154,10,38,24,158,221,37,151,184,52,224,109,73,38,75,31])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGu_Supplied.length2];decide) read08
  simp only [show 60#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGu_Supplied.nodes2 9#usize 8#usize=
        ok (.Next (s09 s) 10#usize 9#usize) := by
    rw [selected08]
    exact JGu_ParentCalls2.source118 D hash (s08 s) 10#usize 3456#usize 60#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 3456 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 3424 v08
      60#u32 8#usize (encodeState value118) 3456#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGu_Supplied.nodes2 1#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGu_Supplied.nodes2 2#usize 2#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGu_Supplied.nodes2 3#usize 3#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGu_Supplied.nodes2 4#usize 4#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGu_Supplied.nodes2 5#usize 5#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGu_Supplied.nodes2 7#usize 6#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGu_Supplied.nodes2 8#usize 7#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGu_Supplied.nodes2 9#usize 8#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGu_Supplied.nodes2 10#usize 9#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s09 s).n.val≤10;rw [v09.size];decide)
  · exact JGm_TX2_View.finish (s09 s) indices09 values09 3456
      v09 9#usize (by decide)
#print axioms source
end AspisR1.JGu_Level2_10
end
