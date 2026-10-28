import NDO_JGm_TX2_ParentCalls1
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level1_03
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGh_TX2_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes1
def indices00 : List U32 := [1787#u32,2656#u32,5269#u32,6922#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
def values00 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 1787#u32 0#usize (encodeState value048) 1184#usize
 def indices01 : List U32 := [893#u32,2656#u32,5269#u32,6922#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value048,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 2656#u32 1#usize (encodeState value049) 1216#usize
 def indices02 : List U32 := [893#u32,1328#u32,5269#u32,6922#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value048,encodeState value049,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 5269#u32 2#usize (encodeState value050) 1248#usize
 def indices03 : List U32 := [893#u32,1328#u32,2634#u32,6922#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value048,encodeState value049,encodeState value050,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 6922#u32 3#usize (encodeState value051) 1280#usize
 def indices04 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value048,encodeState value049,encodeState value050,encodeState value051,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 7982#u32 4#usize (encodeState value052) 1312#usize
 def indices05 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value048,encodeState value049,encodeState value050,encodeState value051,encodeState value052,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 16544#u32 5#usize (encodeState value053) 1344#usize
 def indices06 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value048,encodeState value049,encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 18703#u32 6#usize (encodeState value054) 1376#usize
 def indices07 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value048,encodeState value049,encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 20770#u32 7#usize (encodeState value055) 1408#usize
 def indices08 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value048,encodeState value049,encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value044,encodeState value045,encodeState value046,encodeState value047]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 22260#u32 8#usize (encodeState value056) 1440#usize
 def indices09 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,22452#u32,23204#u32,27261#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value048,encodeState value049,encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value045,encodeState value046,encodeState value047]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 22452#u32 9#usize (encodeState value057) 1472#usize
 def indices10 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,23204#u32,27261#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value048,encodeState value049,encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value046,encodeState value047]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 23204#u32 10#usize (encodeState value058) 1504#usize
 def indices11 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,27261#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value048,encodeState value049,encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value047]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 27261#u32 11#usize (encodeState value059) 1536#usize
 def indices12 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value048,encodeState value049,encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value048,encodeState value049,encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 1152) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 1536 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 1152 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 1787#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 1152 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value036) :=
    JGm_TX2_View.value (s00 s) indices00 values00 1152 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=1152#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠1787#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2656#u32,JGm_TX2_View.index (s00 s) indices00 values00 1152 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s00 s).«at» 1184#usize)=ok (encodeState (JGc_TX2_HashBytes.state [95,112,58,71,93,88,125,240,170,137,227,56,101,123,134,113,255,6,225,244,251,198,92,231,174,141,56,10,11,165,123,139])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 36
      5216#usize 1152#usize 1184#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings03.k1c036_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes1 0#usize 0#usize 1#usize 1184#usize 4064#usize
    1787#u32 (encodeState value036) (encodeState (JGc_TX2_HashBytes.state [95,112,58,71,93,88,125,240,170,137,227,56,101,123,134,113,255,6,225,244,251,198,92,231,174,141,56,10,11,165,123,139])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read00
  simp only [show 1787#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls1.source048 D hash (s00 s) 1#usize 1184#usize 1787#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 1184 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 1152 v00
      1787#u32 0#usize (encodeState value048) 1184#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 2656#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 1184 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value037) :=
    JGm_TX2_View.value (s01 s) indices01 values01 1184 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=1184#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠2656#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨5269#u32,JGm_TX2_View.index (s01 s) indices01 values01 1184 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s01 s).«at» 1216#usize)=ok (encodeState (JGc_TX2_HashBytes.state [58,4,247,132,130,229,131,24,92,198,44,177,234,99,135,67,26,244,113,252,208,248,214,148,174,205,214,74,188,170,27,195])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 37
      5216#usize 1184#usize 1216#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings03.k1c037_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes1 1#usize 1#usize 2#usize 1216#usize 4032#usize
    2656#u32 (encodeState value037) (encodeState (JGc_TX2_HashBytes.state [58,4,247,132,130,229,131,24,92,198,44,177,234,99,135,67,26,244,113,252,208,248,214,148,174,205,214,74,188,170,27,195])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read01
  simp only [show 2656#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls1.source049 D hash (s01 s) 2#usize 1216#usize 2656#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 1216 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 1184 v01
      2656#u32 1#usize (encodeState value049) 1216#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 5269#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 1216 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value038) :=
    JGm_TX2_View.value (s02 s) indices02 values02 1216 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=1216#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠5269#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨6922#u32,JGm_TX2_View.index (s02 s) indices02 values02 1216 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s02 s).«at» 1248#usize)=ok (encodeState (JGc_TX2_HashBytes.state [0,120,208,60,235,45,37,35,176,63,191,234,3,10,87,94,213,75,190,23,105,76,185,25,136,55,233,134,186,180,205,200])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 38
      5216#usize 1216#usize 1248#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings03.k1c038_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes1 2#usize 2#usize 3#usize 1248#usize 4000#usize
    5269#u32 (encodeState value038) (encodeState (JGc_TX2_HashBytes.state [0,120,208,60,235,45,37,35,176,63,191,234,3,10,87,94,213,75,190,23,105,76,185,25,136,55,233,134,186,180,205,200])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read02
  simp only [show 5269#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls1.source050 D hash (s02 s) 3#usize 1248#usize 5269#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 1248 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 1216 v02
      5269#u32 2#usize (encodeState value050) 1248#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 6922#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 1248 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value039) :=
    JGm_TX2_View.value (s03 s) indices03 values03 1248 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=1248#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠6922#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨7982#u32,JGm_TX2_View.index (s03 s) indices03 values03 1248 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s03 s).«at» 1280#usize)=ok (encodeState (JGc_TX2_HashBytes.state [235,146,137,239,114,9,74,180,253,134,12,59,180,148,144,129,96,30,255,141,127,159,144,59,253,107,189,65,75,154,28,189])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 39
      5216#usize 1248#usize 1280#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings03.k1c039_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes1 3#usize 3#usize 4#usize 1280#usize 3968#usize
    6922#u32 (encodeState value039) (encodeState (JGc_TX2_HashBytes.state [235,146,137,239,114,9,74,180,253,134,12,59,180,148,144,129,96,30,255,141,127,159,144,59,253,107,189,65,75,154,28,189])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read03
  simp only [show 6922#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls1.source051 D hash (s03 s) 4#usize 1280#usize 6922#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 1280 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 1248 v03
      6922#u32 3#usize (encodeState value051) 1280#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 7982#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 1280 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value040) :=
    JGm_TX2_View.value (s04 s) indices04 values04 1280 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=1280#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠7982#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨16544#u32,JGm_TX2_View.index (s04 s) indices04 values04 1280 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s04 s).«at» 1312#usize)=ok (encodeState (JGc_TX2_HashBytes.state [169,111,69,169,26,211,162,115,15,217,201,74,82,62,66,178,97,193,204,151,148,29,204,99,127,25,12,104,233,192,4,89])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 40
      5216#usize 1280#usize 1312#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings03.k1c040_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes1 4#usize 4#usize 5#usize 1312#usize 3936#usize
    7982#u32 (encodeState value040) (encodeState (JGc_TX2_HashBytes.state [169,111,69,169,26,211,162,115,15,217,201,74,82,62,66,178,97,193,204,151,148,29,204,99,127,25,12,104,233,192,4,89])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read04
  simp only [show 7982#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls1.source052 D hash (s04 s) 5#usize 1312#usize 7982#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 1312 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 1280 v04
      7982#u32 4#usize (encodeState value052) 1312#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 16544#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 1312 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value041) :=
    JGm_TX2_View.value (s05 s) indices05 values05 1312 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=1312#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠16544#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨18703#u32,JGm_TX2_View.index (s05 s) indices05 values05 1312 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s05 s).«at» 1344#usize)=ok (encodeState (JGc_TX2_HashBytes.state [29,185,194,216,179,1,247,11,172,171,19,55,212,131,32,115,68,44,21,12,219,69,52,197,56,96,77,242,92,83,170,197])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 41
      5216#usize 1312#usize 1344#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings03.k1c041_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes1 5#usize 5#usize 6#usize 1344#usize 3904#usize
    16544#u32 (encodeState value041) (encodeState (JGc_TX2_HashBytes.state [29,185,194,216,179,1,247,11,172,171,19,55,212,131,32,115,68,44,21,12,219,69,52,197,56,96,77,242,92,83,170,197])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read05
  simp only [show 16544#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls1.source053 D hash (s05 s) 6#usize 1344#usize 16544#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 1344 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 1312 v05
      16544#u32 5#usize (encodeState value053) 1344#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 18703#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 1344 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value042) :=
    JGm_TX2_View.value (s06 s) indices06 values06 1344 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=1344#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠18703#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨20770#u32,JGm_TX2_View.index (s06 s) indices06 values06 1344 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s06 s).«at» 1376#usize)=ok (encodeState (JGc_TX2_HashBytes.state [114,13,219,219,217,41,30,52,44,8,66,231,56,144,53,239,114,224,242,236,187,253,218,88,104,60,23,190,61,21,185,131])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 42
      5216#usize 1344#usize 1376#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings03.k1c042_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes1 6#usize 6#usize 7#usize 1376#usize 3872#usize
    18703#u32 (encodeState value042) (encodeState (JGc_TX2_HashBytes.state [114,13,219,219,217,41,30,52,44,8,66,231,56,144,53,239,114,224,242,236,187,253,218,88,104,60,23,190,61,21,185,131])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read06
  simp only [show 18703#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls1.source054 D hash (s06 s) 7#usize 1376#usize 18703#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 1376 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 1344 v06
      18703#u32 6#usize (encodeState value054) 1376#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 20770#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 1376 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value043) :=
    JGm_TX2_View.value (s07 s) indices07 values07 1376 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=1376#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠20770#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨22260#u32,JGm_TX2_View.index (s07 s) indices07 values07 1376 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s07 s).«at» 1408#usize)=ok (encodeState (JGc_TX2_HashBytes.state [240,122,191,34,114,30,58,112,147,135,65,101,141,66,107,30,194,52,193,28,24,107,197,207,126,13,95,174,16,162,166,215])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 43
      5216#usize 1376#usize 1408#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings03.k1c043_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes1 7#usize 7#usize 8#usize 1408#usize 3840#usize
    20770#u32 (encodeState value043) (encodeState (JGc_TX2_HashBytes.state [240,122,191,34,114,30,58,112,147,135,65,101,141,66,107,30,194,52,193,28,24,107,197,207,126,13,95,174,16,162,166,215])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read07
  simp only [show 20770#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls1.source055 D hash (s07 s) 8#usize 1408#usize 20770#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 1408 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 1376 v07
      20770#u32 7#usize (encodeState value055) 1408#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 22260#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 1408 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value044) :=
    JGm_TX2_View.value (s08 s) indices08 values08 1408 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=1408#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠22260#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨22452#u32,JGm_TX2_View.index (s08 s) indices08 values08 1408 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s08 s).«at» 1440#usize)=ok (encodeState (JGc_TX2_HashBytes.state [110,199,41,76,80,253,154,105,34,251,142,152,94,165,80,126,112,246,197,172,144,227,31,251,4,217,88,219,23,237,201,160])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 44
      5216#usize 1408#usize 1440#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings03.k1c044_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes1 8#usize 8#usize 9#usize 1440#usize 3808#usize
    22260#u32 (encodeState value044) (encodeState (JGc_TX2_HashBytes.state [110,199,41,76,80,253,154,105,34,251,142,152,94,165,80,126,112,246,197,172,144,227,31,251,4,217,88,219,23,237,201,160])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read08
  simp only [show 22260#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls1.source056 D hash (s08 s) 9#usize 1440#usize 22260#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 1440 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 1408 v08
      22260#u32 8#usize (encodeState value056) 1440#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 22452#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 1440 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value045) :=
    JGm_TX2_View.value (s09 s) indices09 values09 1440 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=1440#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠22452#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨23204#u32,JGm_TX2_View.index (s09 s) indices09 values09 1440 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s09 s).«at» 1472#usize)=ok (encodeState (JGc_TX2_HashBytes.state [247,163,118,0,246,147,113,68,130,176,157,112,153,88,113,153,219,157,212,173,2,86,74,103,252,248,50,69,161,51,86,188])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 45
      5216#usize 1440#usize 1472#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings03.k1c045_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes1 9#usize 9#usize 10#usize 1472#usize 3776#usize
    22452#u32 (encodeState value045) (encodeState (JGc_TX2_HashBytes.state [247,163,118,0,246,147,113,68,130,176,157,112,153,88,113,153,219,157,212,173,2,86,74,103,252,248,50,69,161,51,86,188])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read09
  simp only [show 22452#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls1.source057 D hash (s09 s) 10#usize 1472#usize 22452#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 1472 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 1440 v09
      22452#u32 9#usize (encodeState value057) 1472#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 23204#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 1472 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value046) :=
    JGm_TX2_View.value (s10 s) indices10 values10 1472 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=1472#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠23204#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨27261#u32,JGm_TX2_View.index (s10 s) indices10 values10 1472 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s10 s).«at» 1504#usize)=ok (encodeState (JGc_TX2_HashBytes.state [52,211,196,240,9,89,152,243,158,210,224,156,42,153,78,220,211,106,118,137,235,6,220,144,243,156,199,95,200,95,194,93])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 46
      5216#usize 1472#usize 1504#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings03.k1c046_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes1 10#usize 10#usize 11#usize 1504#usize 3744#usize
    23204#u32 (encodeState value046) (encodeState (JGc_TX2_HashBytes.state [52,211,196,240,9,89,152,243,158,210,224,156,42,153,78,220,211,106,118,137,235,6,220,144,243,156,199,95,200,95,194,93])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read10
  simp only [show 23204#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes1 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls1.source058 D hash (s10 s) 11#usize 1504#usize 23204#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 1504 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 1472 v10
      23204#u32 10#usize (encodeState value058) 1504#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 27261#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 1504 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value047) :=
    JGm_TX2_View.value (s11 s) indices11 values11 1504 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=1504#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠27261#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s11 s).«at» 1536#usize)=ok (encodeState (JGc_TX2_HashBytes.state [16,42,190,16,201,18,111,225,89,177,137,139,232,23,237,29,155,118,42,57,203,192,229,217,192,251,116,91,3,194,172,187])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 47
      5216#usize 1504#usize 1536#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings03.k1c047_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes1 11#usize 11#usize 12#usize 1536#usize 3712#usize
    27261#u32 (encodeState value047) (encodeState (JGc_TX2_HashBytes.state [16,42,190,16,201,18,111,225,89,177,137,139,232,23,237,29,155,118,42,57,203,192,229,217,192,251,116,91,3,194,172,187])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read11
  simp only [show 27261#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes1 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls1.source059 D hash (s11 s) 12#usize 1536#usize 27261#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 1536 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 1504 v11
      27261#u32 11#usize (encodeState value059) 1536#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGm_TX2_Supplied.nodes1 1#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGm_TX2_Supplied.nodes1 2#usize 2#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGm_TX2_Supplied.nodes1 3#usize 3#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGm_TX2_Supplied.nodes1 4#usize 4#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGm_TX2_Supplied.nodes1 5#usize 5#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGm_TX2_Supplied.nodes1 6#usize 6#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGm_TX2_Supplied.nodes1 7#usize 7#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGm_TX2_Supplied.nodes1 8#usize 8#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGm_TX2_Supplied.nodes1 9#usize 9#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGm_TX2_Supplied.nodes1 10#usize 10#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s) JGm_TX2_Supplied.nodes1 11#usize 11#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active10 row10
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s12 s) JGm_TX2_Supplied.nodes1 12#usize 12#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active11 row11
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s12 s).n.val≤12;rw [v12.size];decide)
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 1536
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level1_03
end
