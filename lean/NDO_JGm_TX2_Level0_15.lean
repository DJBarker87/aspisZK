import NDO_JGm_TX2_ParentCalls0
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level0_15
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGf_TX2_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes0
def indices00 : List U32 := [0#u32,1#u32,4#u32,5#u32,6#u32]
def values00 : List (Array U8 32#usize) := [encodeState value175,encodeState value176,encodeState value177,encodeState value178,encodeState value179]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 0#u32 0#usize (encodeState value180) 5152#usize
 def indices01 : List U32 := [0#u32,1#u32,4#u32,5#u32,6#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value180,encodeState value176,encodeState value177,encodeState value178,encodeState value179]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 4#u32 1#usize (encodeState value181) 5152#usize
 def indices02 : List U32 := [0#u32,2#u32,4#u32,5#u32,6#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value180,encodeState value181,encodeState value177,encodeState value178,encodeState value179]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 6#u32 2#usize (encodeState value182) 5184#usize
 def indices03 : List U32 := [0#u32,2#u32,3#u32,5#u32,6#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value180,encodeState value181,encodeState value182,encodeState value178,encodeState value179]
def output (s : reference.Scratch) : reference.Scratch := {s03 s with n:=3#usize}
 def indicesOut : List U32 := [0#u32,2#u32,3#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value180,encodeState value181,encodeState value182]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 5152) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 5184 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 5152 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 5152 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value175) :=
    JGm_TX2_View.value (s00 s) indices00 values00 5152 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=5152#usize := UScalar.eq_of_val_eq v00.at_eq
  have rn00 : Array.index_usize (s00 s).idx 1#usize=ok (0#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s00 s) indices00 values00 5152 v00 1#usize (by decide)
  have rr00 : Array.index_usize (s00 s).val 1#usize=ok (encodeState value176) :=
    JGm_TX2_View.value (s00 s) indices00 values00 5152 v00 1#usize (by decide)
  have selected00 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes0 0#usize 0#usize 1#usize 2#usize 0#u32
    (encodeState value175) (encodeState value176) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (1:Nat)<(s00 s).n.val;rw [v00.size];decide)
    rn00 rr00 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 2#usize 1#usize) := by
    rw [selected00]
    rw [cursor00]
    exact JGm_TX2_ParentCalls0.source180 D hash (s00 s) 2#usize 5152#usize 0#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 5152 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 5152 v00
      0#u32 0#usize (encodeState value180) 5152#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 2#usize=ok 4#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 5152 v01 2#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 2#usize=ok (encodeState value177) :=
    JGm_TX2_View.value (s01 s) indices01 values01 5152 v01 2#usize (by decide)
  have active01 : 2#usize<(s01 s).n := by
    change (2:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=5152#usize := UScalar.eq_of_val_eq v01.at_eq
  have rn01 : Array.index_usize (s01 s).idx 3#usize=ok (4#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s01 s) indices01 values01 5152 v01 3#usize (by decide)
  have rr01 : Array.index_usize (s01 s).val 3#usize=ok (encodeState value178) :=
    JGm_TX2_View.value (s01 s) indices01 values01 5152 v01 3#usize (by decide)
  have selected01 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes0 2#usize 1#usize 3#usize 4#usize 4#u32
    (encodeState value177) (encodeState value178) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (3:Nat)<(s01 s).n.val;rw [v01.size];decide)
    rn01 rr01 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes0 2#usize 1#usize=
        ok (.Next (s02 s) 4#usize 2#usize) := by
    rw [selected01]
    rw [cursor01]
    exact JGm_TX2_ParentCalls0.source181 D hash (s01 s) 4#usize 5152#usize 4#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 5152 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 5152 v01
      4#u32 1#usize (encodeState value181) 5152#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 4#usize=ok 6#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 5152 v02 4#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 4#usize=ok (encodeState value179) :=
    JGm_TX2_View.value (s02 s) indices02 values02 5152 v02 4#usize (by decide)
  have active02 : 4#usize<(s02 s).n := by
    change (4:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=5152#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 5#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 5#usize=ok other ∧ other≠6#u32 ^^^ 1#u32 := by
    intro more
    change (5:Nat)<(s02 s).n.val at more
    rw [v02.size] at more
    exact False.elim ((by decide : ¬(5:Nat)<5) more)
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s02 s).«at» 5184#usize)=ok (encodeState (JGc_TX2_HashBytes.state [78,76,78,145,83,145,125,165,149,199,20,232,15,8,165,94,236,114,212,6,118,28,230,173,255,46,190,216,0,213,150,249])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 161
      5216#usize 5152#usize 5184#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings15.k0c161_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes0 4#usize 2#usize 5#usize 5184#usize 64#usize
    6#u32 (encodeState value179) (encodeState (JGc_TX2_HashBytes.state [78,76,78,145,83,145,125,165,149,199,20,232,15,8,165,94,236,114,212,6,118,28,230,173,255,46,190,216,0,213,150,249])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read02
  simp only [show 6#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes0 4#usize 2#usize=
        ok (.Next (s03 s) 5#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls0.source182 D hash (s02 s) 5#usize 5184#usize 6#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 5184 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 5152 v02
      6#u32 2#usize (encodeState value182) 5184#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGm_TX2_Supplied.nodes0 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGm_TX2_Supplied.nodes0 2#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGm_TX2_Supplied.nodes0 4#usize 2#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGm_TX2_Supplied.nodes0 5#usize 3#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s03 s).n.val≤5;rw [v03.size];decide)
  · exact JGm_TX2_View.finish (s03 s) indices03 values03 5184
      v03 3#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level0_15
end
