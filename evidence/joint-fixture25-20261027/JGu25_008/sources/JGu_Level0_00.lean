import JGu_ParentCalls0
import JGm_TX2_View
import JGm_TX2_RowControl
import JGm_TX2_ExternalRun
import JGu_Supplied
import JGk_TX2_SiblingLaws
import JFw_Frames
import JFq_Range
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_Level0_00
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGr_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGu_Supplied.nodes0
def indices00 : List U32 := [65593#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32]
def values00 : List (Array U8 32#usize) := [encodeState value006,encodeState value000,encodeState value001,encodeState value009,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 65593#u32 0#usize (encodeState value010) 32#usize
 def indices01 : List U32 := [32796#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value010,encodeState value000,encodeState value001,encodeState value009,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 93499#u32 1#usize (encodeState value011) 64#usize
 def indices02 : List U32 := [32796#u32,46749#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value001,encodeState value009,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 147529#u32 2#usize (encodeState value012) 96#usize
 def indices03 : List U32 := [32796#u32,46749#u32,73764#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value009,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 159813#u32 3#usize (encodeState value013) 128#usize
 def indices04 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 183859#u32 4#usize (encodeState value014) 160#usize
 def indices05 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 192317#u32 5#usize (encodeState value015) 192#usize
 def indices06 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,193093#u32,209371#u32,216823#u32,245899#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 193093#u32 6#usize (encodeState value016) 224#usize
 def indices07 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,209371#u32,216823#u32,245899#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value004,encodeState value002,encodeState value003]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 209371#u32 7#usize (encodeState value017) 256#usize
 def indices08 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,216823#u32,245899#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value002,encodeState value003]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 216823#u32 8#usize (encodeState value018) 288#usize
 def indices09 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,245899#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value003]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 245899#u32 9#usize (encodeState value019) 320#usize
 def indices10 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 0) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGu_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 320 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 0 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 65593#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 0 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value006) :=
    JGm_TX2_View.value (s00 s) indices00 values00 0 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=0#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠65593#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨93499#u32,JGm_TX2_View.index (s00 s) indices00 values00 0 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s00 s).«at» 32#usize)=ok (encodeState (JGc_TX2_HashBytes.state [138,12,78,4,29,195,175,124,49,12,183,253,137,178,1,172,57,105,147,139,13,27,199,21,103,254,125,5,89,218,213,42])) := by
    rw [cursor00]
    unfold JGu_Supplied.nodes0
    rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 0#usize 32#usize (by decide) (by decide)]
    have phys : (MultiproofConeSlices.sub JGp_Slot0.value 0#usize 32#usize).val=
        (encodeState (JGc_TX2_HashBytes.state [138,12,78,4,29,195,175,124,49,12,183,253,137,178,1,172,57,105,147,139,13,27,199,21,103,254,125,5,89,218,213,42])).val := by
      change (((JFw_Frames.window 28359 4672).val.drop 0).take 32)=_
      rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
      change ((JFx_NativeBytes.proof.val.drop 28359).take 32)=(encodeState (JGc_TX2_HashBytes.state [138,12,78,4,29,195,175,124,49,12,183,253,137,178,1,172,57,105,147,139,13,27,199,21,103,254,125,5,89,218,213,42])).val
      simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      rfl
    obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
      (MultiproofConeSlices.sub JGp_Slot0.value 0#usize 32#usize)
      (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [138,12,78,4,29,195,175,124,49,12,183,253,137,178,1,172,57,105,147,139,13,27,199,21,103,254,125,5,89,218,213,42])).property];decide)
    have same : chunk=encodeState (JGc_TX2_HashBytes.state [138,12,78,4,29,195,175,124,49,12,183,253,137,178,1,172,57,105,147,139,13,27,199,21,103,254,125,5,89,218,213,42]) := by
      apply Subtype.ext
      rw [bytes,phys]
      exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [138,12,78,4,29,195,175,124,49,12,183,253,137,178,1,172,57,105,147,139,13,27,199,21,103,254,125,5,89,218,213,42])).property];decide)
    exact same ▸ run
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGu_Supplied.nodes0 0#usize 0#usize 1#usize 32#usize 4416#usize
    65593#u32 (encodeState value006) (encodeState (JGc_TX2_HashBytes.state [138,12,78,4,29,195,175,124,49,12,183,253,137,178,1,172,57,105,147,139,13,27,199,21,103,254,125,5,89,218,213,42])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGu_Supplied.length0];decide) read00
  simp only [show 65593#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGu_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGu_ParentCalls0.source010 D hash (s00 s) 1#usize 32#usize 65593#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 32 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 0 v00
      65593#u32 0#usize (encodeState value010) 32#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 93499#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 32 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value000) :=
    JGm_TX2_View.value (s01 s) indices01 values01 32 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=32#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠93499#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨147529#u32,JGm_TX2_View.index (s01 s) indices01 values01 32 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s01 s).«at» 64#usize)=ok (encodeState (JGc_TX2_HashBytes.state [0,155,210,135,10,10,36,139,250,61,153,156,199,68,178,96,3,25,83,60,150,7,110,64,212,120,34,32,128,70,85,4])) := by
    rw [cursor01]
    unfold JGu_Supplied.nodes0
    rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 32#usize 64#usize (by decide) (by decide)]
    have phys : (MultiproofConeSlices.sub JGp_Slot0.value 32#usize 64#usize).val=
        (encodeState (JGc_TX2_HashBytes.state [0,155,210,135,10,10,36,139,250,61,153,156,199,68,178,96,3,25,83,60,150,7,110,64,212,120,34,32,128,70,85,4])).val := by
      change (((JFw_Frames.window 28359 4672).val.drop 32).take 32)=_
      rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
      change ((JFx_NativeBytes.proof.val.drop 28391).take 32)=(encodeState (JGc_TX2_HashBytes.state [0,155,210,135,10,10,36,139,250,61,153,156,199,68,178,96,3,25,83,60,150,7,110,64,212,120,34,32,128,70,85,4])).val
      simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      rfl
    obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
      (MultiproofConeSlices.sub JGp_Slot0.value 32#usize 64#usize)
      (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [0,155,210,135,10,10,36,139,250,61,153,156,199,68,178,96,3,25,83,60,150,7,110,64,212,120,34,32,128,70,85,4])).property];decide)
    have same : chunk=encodeState (JGc_TX2_HashBytes.state [0,155,210,135,10,10,36,139,250,61,153,156,199,68,178,96,3,25,83,60,150,7,110,64,212,120,34,32,128,70,85,4]) := by
      apply Subtype.ext
      rw [bytes,phys]
      exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [0,155,210,135,10,10,36,139,250,61,153,156,199,68,178,96,3,25,83,60,150,7,110,64,212,120,34,32,128,70,85,4])).property];decide)
    exact same ▸ run
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGu_Supplied.nodes0 1#usize 1#usize 2#usize 64#usize 4384#usize
    93499#u32 (encodeState value000) (encodeState (JGc_TX2_HashBytes.state [0,155,210,135,10,10,36,139,250,61,153,156,199,68,178,96,3,25,83,60,150,7,110,64,212,120,34,32,128,70,85,4])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGu_Supplied.length0];decide) read01
  simp only [show 93499#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGu_Supplied.nodes0 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGu_ParentCalls0.source011 D hash (s01 s) 2#usize 64#usize 93499#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 64 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 32 v01
      93499#u32 1#usize (encodeState value011) 64#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 147529#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 64 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value001) :=
    JGm_TX2_View.value (s02 s) indices02 values02 64 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=64#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠147529#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨159813#u32,JGm_TX2_View.index (s02 s) indices02 values02 64 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s02 s).«at» 96#usize)=ok (encodeState (JGc_TX2_HashBytes.state [30,206,97,181,53,81,203,161,54,188,202,14,118,67,232,27,234,26,123,152,61,193,146,253,243,71,30,207,164,232,190,24])) := by
    rw [cursor02]
    unfold JGu_Supplied.nodes0
    rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 64#usize 96#usize (by decide) (by decide)]
    have phys : (MultiproofConeSlices.sub JGp_Slot0.value 64#usize 96#usize).val=
        (encodeState (JGc_TX2_HashBytes.state [30,206,97,181,53,81,203,161,54,188,202,14,118,67,232,27,234,26,123,152,61,193,146,253,243,71,30,207,164,232,190,24])).val := by
      change (((JFw_Frames.window 28359 4672).val.drop 64).take 32)=_
      rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
      change ((JFx_NativeBytes.proof.val.drop 28423).take 32)=(encodeState (JGc_TX2_HashBytes.state [30,206,97,181,53,81,203,161,54,188,202,14,118,67,232,27,234,26,123,152,61,193,146,253,243,71,30,207,164,232,190,24])).val
      simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      rfl
    obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
      (MultiproofConeSlices.sub JGp_Slot0.value 64#usize 96#usize)
      (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [30,206,97,181,53,81,203,161,54,188,202,14,118,67,232,27,234,26,123,152,61,193,146,253,243,71,30,207,164,232,190,24])).property];decide)
    have same : chunk=encodeState (JGc_TX2_HashBytes.state [30,206,97,181,53,81,203,161,54,188,202,14,118,67,232,27,234,26,123,152,61,193,146,253,243,71,30,207,164,232,190,24]) := by
      apply Subtype.ext
      rw [bytes,phys]
      exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [30,206,97,181,53,81,203,161,54,188,202,14,118,67,232,27,234,26,123,152,61,193,146,253,243,71,30,207,164,232,190,24])).property];decide)
    exact same ▸ run
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGu_Supplied.nodes0 2#usize 2#usize 3#usize 96#usize 4352#usize
    147529#u32 (encodeState value001) (encodeState (JGc_TX2_HashBytes.state [30,206,97,181,53,81,203,161,54,188,202,14,118,67,232,27,234,26,123,152,61,193,146,253,243,71,30,207,164,232,190,24])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGu_Supplied.length0];decide) read02
  simp only [show 147529#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGu_Supplied.nodes0 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGu_ParentCalls0.source012 D hash (s02 s) 3#usize 96#usize 147529#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 96 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 64 v02
      147529#u32 2#usize (encodeState value012) 96#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 159813#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 96 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value009) :=
    JGm_TX2_View.value (s03 s) indices03 values03 96 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=96#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠159813#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨183859#u32,JGm_TX2_View.index (s03 s) indices03 values03 96 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s03 s).«at» 128#usize)=ok (encodeState (JGc_TX2_HashBytes.state [26,195,186,240,93,5,49,188,135,179,131,176,52,102,146,74,221,99,76,219,108,88,144,61,125,193,25,38,125,58,141,31])) := by
    rw [cursor03]
    unfold JGu_Supplied.nodes0
    rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 96#usize 128#usize (by decide) (by decide)]
    have phys : (MultiproofConeSlices.sub JGp_Slot0.value 96#usize 128#usize).val=
        (encodeState (JGc_TX2_HashBytes.state [26,195,186,240,93,5,49,188,135,179,131,176,52,102,146,74,221,99,76,219,108,88,144,61,125,193,25,38,125,58,141,31])).val := by
      change (((JFw_Frames.window 28359 4672).val.drop 96).take 32)=_
      rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
      change ((JFx_NativeBytes.proof.val.drop 28455).take 32)=(encodeState (JGc_TX2_HashBytes.state [26,195,186,240,93,5,49,188,135,179,131,176,52,102,146,74,221,99,76,219,108,88,144,61,125,193,25,38,125,58,141,31])).val
      simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      rfl
    obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
      (MultiproofConeSlices.sub JGp_Slot0.value 96#usize 128#usize)
      (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [26,195,186,240,93,5,49,188,135,179,131,176,52,102,146,74,221,99,76,219,108,88,144,61,125,193,25,38,125,58,141,31])).property];decide)
    have same : chunk=encodeState (JGc_TX2_HashBytes.state [26,195,186,240,93,5,49,188,135,179,131,176,52,102,146,74,221,99,76,219,108,88,144,61,125,193,25,38,125,58,141,31]) := by
      apply Subtype.ext
      rw [bytes,phys]
      exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [26,195,186,240,93,5,49,188,135,179,131,176,52,102,146,74,221,99,76,219,108,88,144,61,125,193,25,38,125,58,141,31])).property];decide)
    exact same ▸ run
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGu_Supplied.nodes0 3#usize 3#usize 4#usize 128#usize 4320#usize
    159813#u32 (encodeState value009) (encodeState (JGc_TX2_HashBytes.state [26,195,186,240,93,5,49,188,135,179,131,176,52,102,146,74,221,99,76,219,108,88,144,61,125,193,25,38,125,58,141,31])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGu_Supplied.length0];decide) read03
  simp only [show 159813#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGu_Supplied.nodes0 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGu_ParentCalls0.source013 D hash (s03 s) 4#usize 128#usize 159813#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 128 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 96 v03
      159813#u32 3#usize (encodeState value013) 128#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 183859#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 128 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value007) :=
    JGm_TX2_View.value (s04 s) indices04 values04 128 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=128#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠183859#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨192317#u32,JGm_TX2_View.index (s04 s) indices04 values04 128 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s04 s).«at» 160#usize)=ok (encodeState (JGc_TX2_HashBytes.state [40,252,149,36,166,192,162,64,101,20,54,49,63,59,166,85,31,38,36,0,99,178,228,189,116,169,252,141,90,193,181,51])) := by
    rw [cursor04]
    unfold JGu_Supplied.nodes0
    rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 128#usize 160#usize (by decide) (by decide)]
    have phys : (MultiproofConeSlices.sub JGp_Slot0.value 128#usize 160#usize).val=
        (encodeState (JGc_TX2_HashBytes.state [40,252,149,36,166,192,162,64,101,20,54,49,63,59,166,85,31,38,36,0,99,178,228,189,116,169,252,141,90,193,181,51])).val := by
      change (((JFw_Frames.window 28359 4672).val.drop 128).take 32)=_
      rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
      change ((JFx_NativeBytes.proof.val.drop 28487).take 32)=(encodeState (JGc_TX2_HashBytes.state [40,252,149,36,166,192,162,64,101,20,54,49,63,59,166,85,31,38,36,0,99,178,228,189,116,169,252,141,90,193,181,51])).val
      simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      rfl
    obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
      (MultiproofConeSlices.sub JGp_Slot0.value 128#usize 160#usize)
      (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [40,252,149,36,166,192,162,64,101,20,54,49,63,59,166,85,31,38,36,0,99,178,228,189,116,169,252,141,90,193,181,51])).property];decide)
    have same : chunk=encodeState (JGc_TX2_HashBytes.state [40,252,149,36,166,192,162,64,101,20,54,49,63,59,166,85,31,38,36,0,99,178,228,189,116,169,252,141,90,193,181,51]) := by
      apply Subtype.ext
      rw [bytes,phys]
      exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [40,252,149,36,166,192,162,64,101,20,54,49,63,59,166,85,31,38,36,0,99,178,228,189,116,169,252,141,90,193,181,51])).property];decide)
    exact same ▸ run
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGu_Supplied.nodes0 4#usize 4#usize 5#usize 160#usize 4288#usize
    183859#u32 (encodeState value007) (encodeState (JGc_TX2_HashBytes.state [40,252,149,36,166,192,162,64,101,20,54,49,63,59,166,85,31,38,36,0,99,178,228,189,116,169,252,141,90,193,181,51])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGu_Supplied.length0];decide) read04
  simp only [show 183859#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGu_Supplied.nodes0 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGu_ParentCalls0.source014 D hash (s04 s) 5#usize 160#usize 183859#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 160 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 128 v04
      183859#u32 4#usize (encodeState value014) 160#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 192317#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 160 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value005) :=
    JGm_TX2_View.value (s05 s) indices05 values05 160 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=160#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠192317#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨193093#u32,JGm_TX2_View.index (s05 s) indices05 values05 160 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s05 s).«at» 192#usize)=ok (encodeState (JGc_TX2_HashBytes.state [197,135,76,25,172,180,98,84,70,211,112,237,137,36,20,194,104,104,114,136,240,147,181,141,121,72,73,200,110,2,159,172])) := by
    rw [cursor05]
    unfold JGu_Supplied.nodes0
    rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 160#usize 192#usize (by decide) (by decide)]
    have phys : (MultiproofConeSlices.sub JGp_Slot0.value 160#usize 192#usize).val=
        (encodeState (JGc_TX2_HashBytes.state [197,135,76,25,172,180,98,84,70,211,112,237,137,36,20,194,104,104,114,136,240,147,181,141,121,72,73,200,110,2,159,172])).val := by
      change (((JFw_Frames.window 28359 4672).val.drop 160).take 32)=_
      rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
      change ((JFx_NativeBytes.proof.val.drop 28519).take 32)=(encodeState (JGc_TX2_HashBytes.state [197,135,76,25,172,180,98,84,70,211,112,237,137,36,20,194,104,104,114,136,240,147,181,141,121,72,73,200,110,2,159,172])).val
      simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      rfl
    obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
      (MultiproofConeSlices.sub JGp_Slot0.value 160#usize 192#usize)
      (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [197,135,76,25,172,180,98,84,70,211,112,237,137,36,20,194,104,104,114,136,240,147,181,141,121,72,73,200,110,2,159,172])).property];decide)
    have same : chunk=encodeState (JGc_TX2_HashBytes.state [197,135,76,25,172,180,98,84,70,211,112,237,137,36,20,194,104,104,114,136,240,147,181,141,121,72,73,200,110,2,159,172]) := by
      apply Subtype.ext
      rw [bytes,phys]
      exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [197,135,76,25,172,180,98,84,70,211,112,237,137,36,20,194,104,104,114,136,240,147,181,141,121,72,73,200,110,2,159,172])).property];decide)
    exact same ▸ run
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGu_Supplied.nodes0 5#usize 5#usize 6#usize 192#usize 4256#usize
    192317#u32 (encodeState value005) (encodeState (JGc_TX2_HashBytes.state [197,135,76,25,172,180,98,84,70,211,112,237,137,36,20,194,104,104,114,136,240,147,181,141,121,72,73,200,110,2,159,172])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGu_Supplied.length0];decide) read05
  simp only [show 192317#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGu_Supplied.nodes0 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGu_ParentCalls0.source015 D hash (s05 s) 6#usize 192#usize 192317#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 192 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 160 v05
      192317#u32 5#usize (encodeState value015) 192#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 193093#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 192 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value008) :=
    JGm_TX2_View.value (s06 s) indices06 values06 192 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=192#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠193093#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨209371#u32,JGm_TX2_View.index (s06 s) indices06 values06 192 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s06 s).«at» 224#usize)=ok (encodeState (JGc_TX2_HashBytes.state [221,112,50,50,72,39,34,4,52,173,152,99,96,65,187,155,71,131,8,35,206,215,205,144,48,160,238,66,13,85,203,152])) := by
    rw [cursor06]
    unfold JGu_Supplied.nodes0
    rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 192#usize 224#usize (by decide) (by decide)]
    have phys : (MultiproofConeSlices.sub JGp_Slot0.value 192#usize 224#usize).val=
        (encodeState (JGc_TX2_HashBytes.state [221,112,50,50,72,39,34,4,52,173,152,99,96,65,187,155,71,131,8,35,206,215,205,144,48,160,238,66,13,85,203,152])).val := by
      change (((JFw_Frames.window 28359 4672).val.drop 192).take 32)=_
      rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
      change ((JFx_NativeBytes.proof.val.drop 28551).take 32)=(encodeState (JGc_TX2_HashBytes.state [221,112,50,50,72,39,34,4,52,173,152,99,96,65,187,155,71,131,8,35,206,215,205,144,48,160,238,66,13,85,203,152])).val
      simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      rfl
    obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
      (MultiproofConeSlices.sub JGp_Slot0.value 192#usize 224#usize)
      (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [221,112,50,50,72,39,34,4,52,173,152,99,96,65,187,155,71,131,8,35,206,215,205,144,48,160,238,66,13,85,203,152])).property];decide)
    have same : chunk=encodeState (JGc_TX2_HashBytes.state [221,112,50,50,72,39,34,4,52,173,152,99,96,65,187,155,71,131,8,35,206,215,205,144,48,160,238,66,13,85,203,152]) := by
      apply Subtype.ext
      rw [bytes,phys]
      exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [221,112,50,50,72,39,34,4,52,173,152,99,96,65,187,155,71,131,8,35,206,215,205,144,48,160,238,66,13,85,203,152])).property];decide)
    exact same ▸ run
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGu_Supplied.nodes0 6#usize 6#usize 7#usize 224#usize 4224#usize
    193093#u32 (encodeState value008) (encodeState (JGc_TX2_HashBytes.state [221,112,50,50,72,39,34,4,52,173,152,99,96,65,187,155,71,131,8,35,206,215,205,144,48,160,238,66,13,85,203,152])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGu_Supplied.length0];decide) read06
  simp only [show 193093#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGu_Supplied.nodes0 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGu_ParentCalls0.source016 D hash (s06 s) 7#usize 224#usize 193093#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 224 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 192 v06
      193093#u32 6#usize (encodeState value016) 224#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 209371#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 224 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value004) :=
    JGm_TX2_View.value (s07 s) indices07 values07 224 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=224#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠209371#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨216823#u32,JGm_TX2_View.index (s07 s) indices07 values07 224 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s07 s).«at» 256#usize)=ok (encodeState (JGc_TX2_HashBytes.state [98,52,222,92,145,216,45,125,153,221,152,251,15,144,137,56,230,174,11,161,151,249,216,185,201,144,36,136,166,73,211,28])) := by
    rw [cursor07]
    unfold JGu_Supplied.nodes0
    rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 224#usize 256#usize (by decide) (by decide)]
    have phys : (MultiproofConeSlices.sub JGp_Slot0.value 224#usize 256#usize).val=
        (encodeState (JGc_TX2_HashBytes.state [98,52,222,92,145,216,45,125,153,221,152,251,15,144,137,56,230,174,11,161,151,249,216,185,201,144,36,136,166,73,211,28])).val := by
      change (((JFw_Frames.window 28359 4672).val.drop 224).take 32)=_
      rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
      change ((JFx_NativeBytes.proof.val.drop 28583).take 32)=(encodeState (JGc_TX2_HashBytes.state [98,52,222,92,145,216,45,125,153,221,152,251,15,144,137,56,230,174,11,161,151,249,216,185,201,144,36,136,166,73,211,28])).val
      simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      rfl
    obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
      (MultiproofConeSlices.sub JGp_Slot0.value 224#usize 256#usize)
      (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [98,52,222,92,145,216,45,125,153,221,152,251,15,144,137,56,230,174,11,161,151,249,216,185,201,144,36,136,166,73,211,28])).property];decide)
    have same : chunk=encodeState (JGc_TX2_HashBytes.state [98,52,222,92,145,216,45,125,153,221,152,251,15,144,137,56,230,174,11,161,151,249,216,185,201,144,36,136,166,73,211,28]) := by
      apply Subtype.ext
      rw [bytes,phys]
      exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [98,52,222,92,145,216,45,125,153,221,152,251,15,144,137,56,230,174,11,161,151,249,216,185,201,144,36,136,166,73,211,28])).property];decide)
    exact same ▸ run
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGu_Supplied.nodes0 7#usize 7#usize 8#usize 256#usize 4192#usize
    209371#u32 (encodeState value004) (encodeState (JGc_TX2_HashBytes.state [98,52,222,92,145,216,45,125,153,221,152,251,15,144,137,56,230,174,11,161,151,249,216,185,201,144,36,136,166,73,211,28])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGu_Supplied.length0];decide) read07
  simp only [show 209371#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGu_Supplied.nodes0 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGu_ParentCalls0.source017 D hash (s07 s) 8#usize 256#usize 209371#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 256 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 224 v07
      209371#u32 7#usize (encodeState value017) 256#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 216823#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 256 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value002) :=
    JGm_TX2_View.value (s08 s) indices08 values08 256 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=256#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠216823#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨245899#u32,JGm_TX2_View.index (s08 s) indices08 values08 256 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s08 s).«at» 288#usize)=ok (encodeState (JGc_TX2_HashBytes.state [60,239,18,111,191,102,204,179,135,84,19,39,39,192,93,82,21,159,129,98,135,224,200,173,184,187,89,90,164,245,183,28])) := by
    rw [cursor08]
    unfold JGu_Supplied.nodes0
    rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 256#usize 288#usize (by decide) (by decide)]
    have phys : (MultiproofConeSlices.sub JGp_Slot0.value 256#usize 288#usize).val=
        (encodeState (JGc_TX2_HashBytes.state [60,239,18,111,191,102,204,179,135,84,19,39,39,192,93,82,21,159,129,98,135,224,200,173,184,187,89,90,164,245,183,28])).val := by
      change (((JFw_Frames.window 28359 4672).val.drop 256).take 32)=_
      rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
      change ((JFx_NativeBytes.proof.val.drop 28615).take 32)=(encodeState (JGc_TX2_HashBytes.state [60,239,18,111,191,102,204,179,135,84,19,39,39,192,93,82,21,159,129,98,135,224,200,173,184,187,89,90,164,245,183,28])).val
      simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      rfl
    obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
      (MultiproofConeSlices.sub JGp_Slot0.value 256#usize 288#usize)
      (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [60,239,18,111,191,102,204,179,135,84,19,39,39,192,93,82,21,159,129,98,135,224,200,173,184,187,89,90,164,245,183,28])).property];decide)
    have same : chunk=encodeState (JGc_TX2_HashBytes.state [60,239,18,111,191,102,204,179,135,84,19,39,39,192,93,82,21,159,129,98,135,224,200,173,184,187,89,90,164,245,183,28]) := by
      apply Subtype.ext
      rw [bytes,phys]
      exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [60,239,18,111,191,102,204,179,135,84,19,39,39,192,93,82,21,159,129,98,135,224,200,173,184,187,89,90,164,245,183,28])).property];decide)
    exact same ▸ run
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGu_Supplied.nodes0 8#usize 8#usize 9#usize 288#usize 4160#usize
    216823#u32 (encodeState value002) (encodeState (JGc_TX2_HashBytes.state [60,239,18,111,191,102,204,179,135,84,19,39,39,192,93,82,21,159,129,98,135,224,200,173,184,187,89,90,164,245,183,28])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGu_Supplied.length0];decide) read08
  simp only [show 216823#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGu_Supplied.nodes0 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGu_ParentCalls0.source018 D hash (s08 s) 9#usize 288#usize 216823#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 288 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 256 v08
      216823#u32 8#usize (encodeState value018) 288#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 245899#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 288 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value003) :=
    JGm_TX2_View.value (s09 s) indices09 values09 288 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=288#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠245899#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes0
      (s09 s).«at» 320#usize)=ok (encodeState (JGc_TX2_HashBytes.state [2,236,210,68,67,97,179,9,220,150,3,95,165,1,185,29,159,221,4,51,208,1,32,211,224,128,53,137,65,4,60,189])) := by
    rw [cursor09]
    unfold JGu_Supplied.nodes0
    rw [JGm_TX2_Supplied.sub_prefix JGp_Slot0.value 4416#usize 288#usize 320#usize (by decide) (by decide)]
    have phys : (MultiproofConeSlices.sub JGp_Slot0.value 288#usize 320#usize).val=
        (encodeState (JGc_TX2_HashBytes.state [2,236,210,68,67,97,179,9,220,150,3,95,165,1,185,29,159,221,4,51,208,1,32,211,224,128,53,137,65,4,60,189])).val := by
      change (((JFw_Frames.window 28359 4672).val.drop 288).take 32)=_
      rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
      change ((JFx_NativeBytes.proof.val.drop 28647).take 32)=(encodeState (JGc_TX2_HashBytes.state [2,236,210,68,67,97,179,9,220,150,3,95,165,1,185,29,159,221,4,51,208,1,32,211,224,128,53,137,65,4,60,189])).val
      simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      simp only [JFx_DataProof07.bytes,JFx_DataProof07.c00_length,JFx_DataProof07.c01_length,JFx_DataProof07.c02_length,JFx_DataProof07.c03_length,JFx_DataProof07.c04_length,JFx_DataProof07.c05_length,JFx_DataProof07.c06_length,JFx_DataProof07.c07_length,JFx_DataProof07.c08_length,JFx_DataProof07.c09_length,JFx_DataProof07.c10_length,JFx_DataProof07.c11_length,JFx_DataProof07.c12_length,JFx_DataProof07.c13_length,JFx_DataProof07.c14_length,JFx_DataProof07.c15_length,JFx_DataProof07.c16_length,JFx_DataProof07.c17_length,JFx_DataProof07.c18_length,JFx_DataProof07.c19_length,JFx_DataProof07.c20_length,JFx_DataProof07.c21_length,JFx_DataProof07.c22_length,JFx_DataProof07.c23_length,JFx_DataProof07.c24_length,JFx_DataProof07.c25_length,JFx_DataProof07.c26_length,JFx_DataProof07.c27_length,JFx_DataProof07.c28_length,JFx_DataProof07.c29_length,JFx_DataProof07.c30_length,JFx_DataProof07.c31_length,JFx_DataProof07.c32_length,JFx_DataProof07.c33_length,JFx_DataProof07.c34_length,JFx_DataProof07.c35_length,JFx_DataProof07.c36_length,JFx_DataProof07.c37_length,JFx_DataProof07.c38_length,JFx_DataProof07.c39_length,JFx_DataProof07.c40_length,JFx_DataProof07.c41_length,JFx_DataProof07.c42_length,JFx_DataProof07.c43_length,JFx_DataProof07.c44_length,JFx_DataProof07.c45_length,JFx_DataProof07.c46_length,JFx_DataProof07.c47_length,JFx_DataProof07.c48_length,JFx_DataProof07.c49_length,JFx_DataProof07.c50_length,JFx_DataProof07.c51_length,JFx_DataProof07.c52_length,JFx_DataProof07.c53_length,JFx_DataProof07.c54_length,JFx_DataProof07.c55_length,JFx_DataProof07.c56_length,JFx_DataProof07.c57_length,JFx_DataProof07.c58_length,JFx_DataProof07.c59_length,JFx_DataProof07.c60_length,JFx_DataProof07.c61_length,JFx_DataProof07.c62_length,JFx_DataProof07.c63_length,JFx_DataProof07.c64_length,JFx_DataProof07.c65_length,JFx_DataProof07.c66_length,JFx_DataProof07.c67_length,JFx_DataProof07.c68_length,JFx_DataProof07.c69_length,JFx_DataProof07.c70_length,JFx_DataProof07.c71_length,JFx_DataProof07.c72_length,JFx_DataProof07.c73_length,JFx_DataProof07.c74_length,JFx_DataProof07.c75_length,JFx_DataProof07.c76_length,JFx_DataProof07.c77_length,JFx_DataProof07.c78_length,JFx_DataProof07.c79_length,JFx_DataProof07.c80_length,JFx_DataProof07.c81_length,JFx_DataProof07.c82_length,JFx_DataProof07.c83_length,JFx_DataProof07.c84_length,JFx_DataProof07.c85_length,JFx_DataProof07.c86_length,JFx_DataProof07.c87_length,JFx_DataProof07.c88_length,JFx_DataProof07.c89_length,JFx_DataProof07.c90_length,JFx_DataProof07.c91_length,JFx_DataProof07.c92_length,JFx_DataProof07.c93_length,JFx_DataProof07.c94_length,JFx_DataProof07.c95_length,JFx_DataProof07.c96_length,JFx_DataProof07.c97_length,JFx_DataProof07.c98_length,JFx_DataProof07.c99_length,JFx_DataProof07.c100_length,JFx_DataProof07.c101_length,JFx_DataProof07.c102_length,JFx_DataProof07.c103_length,JFx_DataProof07.c104_length,JFx_DataProof07.c105_length,JFx_DataProof07.c106_length,JFx_DataProof07.c107_length,JFx_DataProof07.c108_length,JFx_DataProof07.c109_length,JFx_DataProof07.c110_length,JFx_DataProof07.c111_length,JFx_DataProof07.c112_length,JFx_DataProof07.c113_length,JFx_DataProof07.c114_length,JFx_DataProof07.c115_length,JFx_DataProof07.c116_length,JFx_DataProof07.c117_length,JFx_DataProof07.c118_length,JFx_DataProof07.c119_length,JFx_DataProof07.c120_length,JFx_DataProof07.c121_length,JFx_DataProof07.c122_length,JFx_DataProof07.c123_length,JFx_DataProof07.c124_length,JFx_DataProof07.c125_length,JFx_DataProof07.c126_length,JFx_DataProof07.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
      rfl
    obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
      (MultiproofConeSlices.sub JGp_Slot0.value 288#usize 320#usize)
      (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [2,236,210,68,67,97,179,9,220,150,3,95,165,1,185,29,159,221,4,51,208,1,32,211,224,128,53,137,65,4,60,189])).property];decide)
    have same : chunk=encodeState (JGc_TX2_HashBytes.state [2,236,210,68,67,97,179,9,220,150,3,95,165,1,185,29,159,221,4,51,208,1,32,211,224,128,53,137,65,4,60,189]) := by
      apply Subtype.ext
      rw [bytes,phys]
      exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [2,236,210,68,67,97,179,9,220,150,3,95,165,1,185,29,159,221,4,51,208,1,32,211,224,128,53,137,65,4,60,189])).property];decide)
    exact same ▸ run
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGu_Supplied.nodes0 9#usize 9#usize 10#usize 320#usize 4128#usize
    245899#u32 (encodeState value003) (encodeState (JGc_TX2_HashBytes.state [2,236,210,68,67,97,179,9,220,150,3,95,165,1,185,29,159,221,4,51,208,1,32,211,224,128,53,137,65,4,60,189])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGu_Supplied.nodes0=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length0
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGu_Supplied.length0];decide) read09
  simp only [show 245899#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGu_Supplied.nodes0 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGu_ParentCalls0.source019 D hash (s09 s) 10#usize 320#usize 245899#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 320 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 288 v09
      245899#u32 9#usize (encodeState value019) 320#usize (by decide)
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
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 320
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JGu_Level0_00
end
