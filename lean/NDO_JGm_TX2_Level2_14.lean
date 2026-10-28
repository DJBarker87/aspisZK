import NDO_JGm_TX2_ParentCalls2
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level2_14
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGc_TX2_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes2
def indices00 : List U32 := [0#u32,2#u32,3#u32]
def values00 : List (Array U8 32#usize) := [encodeState value156,encodeState value157,encodeState value158]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 0#u32 0#usize (encodeState value159) 4448#usize
 def indices01 : List U32 := [0#u32,2#u32,3#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value159,encodeState value157,encodeState value158]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 2#u32 1#usize (encodeState value160) 4448#usize
 def indices02 : List U32 := [0#u32,1#u32,3#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value159,encodeState value160,encodeState value158]
def output (s : reference.Scratch) : reference.Scratch := {s02 s with n:=2#usize}
 def indicesOut : List U32 := [0#u32,1#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value159,encodeState value160]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 4416) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 4448 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 4416 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 4416 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value156) :=
    JGm_TX2_View.value (s00 s) indices00 values00 4416 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=4416#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠0#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2#u32,JGm_TX2_View.index (s00 s) indices00 values00 4416 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s00 s).«at» 4448#usize)=ok (encodeState (JGc_TX2_HashBytes.state [228,96,201,65,47,217,114,210,72,6,233,71,93,13,177,139,113,68,25,125,252,162,191,55,162,47,84,136,175,38,253,181])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 138
      4512#usize 4416#usize 4448#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings14.k2c138_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes2 0#usize 0#usize 1#usize 4448#usize 96#usize
    0#u32 (encodeState value156) (encodeState (JGc_TX2_HashBytes.state [228,96,201,65,47,217,114,210,72,6,233,71,93,13,177,139,113,68,25,125,252,162,191,55,162,47,84,136,175,38,253,181])) ri00 rv00
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
    exact JGm_TX2_ParentCalls2.source159 D hash (s00 s) 1#usize 4448#usize 0#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 4448 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 4416 v00
      0#u32 0#usize (encodeState value159) 4448#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 2#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 4448 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value157) :=
    JGm_TX2_View.value (s01 s) indices01 values01 4448 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=4448#usize := UScalar.eq_of_val_eq v01.at_eq
  have rn01 : Array.index_usize (s01 s).idx 2#usize=ok (2#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s01 s) indices01 values01 4448 v01 2#usize (by decide)
  have rr01 : Array.index_usize (s01 s).val 2#usize=ok (encodeState value158) :=
    JGm_TX2_View.value (s01 s) indices01 values01 4448 v01 2#usize (by decide)
  have selected01 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes2 1#usize 1#usize 2#usize 3#usize 2#u32
    (encodeState value157) (encodeState value158) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (2:Nat)<(s01 s).n.val;rw [v01.size];decide)
    rn01 rr01 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 3#usize 2#usize) := by
    rw [selected01]
    rw [cursor01]
    exact JGm_TX2_ParentCalls2.source160 D hash (s01 s) 3#usize 4448#usize 2#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 4448 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 4448 v01
      2#u32 1#usize (encodeState value160) 4448#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGm_TX2_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGm_TX2_Supplied.nodes2 1#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGm_TX2_Supplied.nodes2 3#usize 2#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s02 s).n.val≤3;rw [v02.size];decide)
  · exact JGm_TX2_View.finish (s02 s) indices02 values02 4448
      v02 2#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level2_14
end
