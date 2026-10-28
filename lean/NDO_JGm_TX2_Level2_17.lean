import NDO_JGm_TX2_ParentCalls2
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level2_17
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGc_TX2_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes2
def indices00 : List U32 := [0#u32]
def values00 : List (Array U8 32#usize) := [encodeState value162]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 0#u32 0#usize (encodeState value163) 4512#usize
 def indices01 : List U32 := [0#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value163]
def output (s : reference.Scratch) : reference.Scratch := {s01 s with n:=1#usize}
 def indicesOut : List U32 := [0#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value163]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 4480) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 4512 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 4480 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 4480 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value162) :=
    JGm_TX2_View.value (s00 s) indices00 values00 4480 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=4480#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠0#u32 ^^^ 1#u32 := by
    intro more
    change (1:Nat)<(s00 s).n.val at more
    rw [v00.size] at more
    exact False.elim ((by decide : ¬(1:Nat)<1) more)
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s00 s).«at» 4512#usize)=ok (encodeState (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 140
      4512#usize 4480#usize 4512#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings17.k2c140_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes2 0#usize 0#usize 1#usize 4512#usize 32#usize
    0#u32 (encodeState value162) (encodeState (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read00
  simp only [show 0#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls2.source163 D hash (s00 s) 1#usize 4512#usize 0#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 4512 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 4480 v00
      0#u32 0#usize (encodeState value163) 4512#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGm_TX2_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGm_TX2_Supplied.nodes2 1#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s01 s).n.val≤1;rw [v01.size];decide)
  · exact JGm_TX2_View.finish (s01 s) indices01 values01 4512
      v01 1#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level2_17
end
