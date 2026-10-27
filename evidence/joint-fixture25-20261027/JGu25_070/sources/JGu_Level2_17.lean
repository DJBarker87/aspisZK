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
namespace AspisR1.JGu_Level2_17
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGu_Supplied.nodes2
def indices00 : List U32 := [0#u32]
def values00 : List (Array U8 32#usize) := [encodeState value137]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 0#u32 0#usize (encodeState value138) 3840#usize
 def indices01 : List U32 := [0#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value138]
def output (s : reference.Scratch) : reference.Scratch := {s01 s with n:=1#usize}
 def indicesOut : List U32 := [0#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value138]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      3808#usize 3840#usize)=ok (encodeState (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80])) := by
  unfold JGu_Supplied.nodes2
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 3808#usize 3840#usize (by decide) (by decide)]
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
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
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
  have read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes2
      (s00 s).«at» 3840#usize)=ok (encodeState (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGu_Supplied.nodes2 0#usize 0#usize 1#usize 3840#usize 32#usize
    0#u32 (encodeState value137) (encodeState (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGu_Supplied.length2];decide) read00
  simp only [show 0#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGu_ParentCalls2.source138 D hash (s00 s) 1#usize 3840#usize 0#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3840 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3808 v00
      0#u32 0#usize (encodeState value138) 3840#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGu_Supplied.nodes2 1#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s01 s).n.val≤1;rw [v01.size];decide)
  · exact JGm_TX2_View.finish (s01 s) indices01 values01 3840
      v01 1#usize (by decide)
#print axioms source
end AspisR1.JGu_Level2_17
end
