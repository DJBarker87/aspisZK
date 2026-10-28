import NDO_JGm_TX2_ParentCalls2
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level2_01
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGc_TX2_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes2
def indices00 : List U32 := [1787#u32,2656#u32,5269#u32,6922#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
def values00 : List (Array U8 32#usize) := [encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019,encodeState value020,encodeState value021,encodeState value022,encodeState value023]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 1787#u32 0#usize (encodeState value024) 416#usize
 def indices01 : List U32 := [893#u32,2656#u32,5269#u32,6922#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value024,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019,encodeState value020,encodeState value021,encodeState value022,encodeState value023]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 2656#u32 1#usize (encodeState value025) 448#usize
 def indices02 : List U32 := [893#u32,1328#u32,5269#u32,6922#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value024,encodeState value025,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019,encodeState value020,encodeState value021,encodeState value022,encodeState value023]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 5269#u32 2#usize (encodeState value026) 480#usize
 def indices03 : List U32 := [893#u32,1328#u32,2634#u32,6922#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value024,encodeState value025,encodeState value026,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019,encodeState value020,encodeState value021,encodeState value022,encodeState value023]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 6922#u32 3#usize (encodeState value027) 512#usize
 def indices04 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value016,encodeState value017,encodeState value018,encodeState value019,encodeState value020,encodeState value021,encodeState value022,encodeState value023]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 7982#u32 4#usize (encodeState value028) 544#usize
 def indices05 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value017,encodeState value018,encodeState value019,encodeState value020,encodeState value021,encodeState value022,encodeState value023]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 16544#u32 5#usize (encodeState value029) 576#usize
 def indices06 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029,encodeState value018,encodeState value019,encodeState value020,encodeState value021,encodeState value022,encodeState value023]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 18703#u32 6#usize (encodeState value030) 608#usize
 def indices07 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value019,encodeState value020,encodeState value021,encodeState value022,encodeState value023]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 20770#u32 7#usize (encodeState value031) 640#usize
 def indices08 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value020,encodeState value021,encodeState value022,encodeState value023]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 22260#u32 8#usize (encodeState value032) 672#usize
 def indices09 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,22452#u32,23204#u32,27261#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value021,encodeState value022,encodeState value023]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 22452#u32 9#usize (encodeState value033) 704#usize
 def indices10 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,23204#u32,27261#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value022,encodeState value023]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 23204#u32 10#usize (encodeState value034) 736#usize
 def indices11 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,27261#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value023]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 27261#u32 11#usize (encodeState value035) 768#usize
 def indices12 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 384) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 768 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 384 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 1787#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 384 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value012) :=
    JGm_TX2_View.value (s00 s) indices00 values00 384 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=384#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠1787#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2656#u32,JGm_TX2_View.index (s00 s) indices00 values00 384 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s00 s).«at» 416#usize)=ok (encodeState (JGc_TX2_HashBytes.state [105,35,33,25,119,208,99,122,241,83,137,249,1,36,19,102,132,128,84,40,134,172,5,189,221,115,114,23,3,37,54,158])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 12
      4512#usize 384#usize 416#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings01.k2c012_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes2 0#usize 0#usize 1#usize 416#usize 4128#usize
    1787#u32 (encodeState value012) (encodeState (JGc_TX2_HashBytes.state [105,35,33,25,119,208,99,122,241,83,137,249,1,36,19,102,132,128,84,40,134,172,5,189,221,115,114,23,3,37,54,158])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read00
  simp only [show 1787#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls2.source024 D hash (s00 s) 1#usize 416#usize 1787#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 416 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 384 v00
      1787#u32 0#usize (encodeState value024) 416#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 2656#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 416 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value013) :=
    JGm_TX2_View.value (s01 s) indices01 values01 416 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=416#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠2656#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨5269#u32,JGm_TX2_View.index (s01 s) indices01 values01 416 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s01 s).«at» 448#usize)=ok (encodeState (JGc_TX2_HashBytes.state [218,176,44,113,131,180,132,20,212,56,12,158,193,73,217,66,162,155,35,24,129,247,189,168,103,224,224,11,223,60,137,215])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 13
      4512#usize 416#usize 448#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings01.k2c013_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes2 1#usize 1#usize 2#usize 448#usize 4096#usize
    2656#u32 (encodeState value013) (encodeState (JGc_TX2_HashBytes.state [218,176,44,113,131,180,132,20,212,56,12,158,193,73,217,66,162,155,35,24,129,247,189,168,103,224,224,11,223,60,137,215])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read01
  simp only [show 2656#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls2.source025 D hash (s01 s) 2#usize 448#usize 2656#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 448 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 416 v01
      2656#u32 1#usize (encodeState value025) 448#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 5269#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 448 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value014) :=
    JGm_TX2_View.value (s02 s) indices02 values02 448 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=448#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠5269#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨6922#u32,JGm_TX2_View.index (s02 s) indices02 values02 448 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s02 s).«at» 480#usize)=ok (encodeState (JGc_TX2_HashBytes.state [132,255,46,148,119,0,171,127,165,204,158,201,240,96,58,157,230,188,33,239,24,211,136,255,49,109,40,245,11,18,140,22])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 14
      4512#usize 448#usize 480#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings01.k2c014_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes2 2#usize 2#usize 3#usize 480#usize 4064#usize
    5269#u32 (encodeState value014) (encodeState (JGc_TX2_HashBytes.state [132,255,46,148,119,0,171,127,165,204,158,201,240,96,58,157,230,188,33,239,24,211,136,255,49,109,40,245,11,18,140,22])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read02
  simp only [show 5269#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls2.source026 D hash (s02 s) 3#usize 480#usize 5269#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 480 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 448 v02
      5269#u32 2#usize (encodeState value026) 480#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 6922#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 480 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value015) :=
    JGm_TX2_View.value (s03 s) indices03 values03 480 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=480#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠6922#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨7982#u32,JGm_TX2_View.index (s03 s) indices03 values03 480 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s03 s).«at» 512#usize)=ok (encodeState (JGc_TX2_HashBytes.state [85,215,10,4,191,215,234,187,84,233,203,164,88,121,188,115,84,133,133,163,100,71,185,145,61,125,215,5,244,103,15,220])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 15
      4512#usize 480#usize 512#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings01.k2c015_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes2 3#usize 3#usize 4#usize 512#usize 4032#usize
    6922#u32 (encodeState value015) (encodeState (JGc_TX2_HashBytes.state [85,215,10,4,191,215,234,187,84,233,203,164,88,121,188,115,84,133,133,163,100,71,185,145,61,125,215,5,244,103,15,220])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read03
  simp only [show 6922#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes2 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls2.source027 D hash (s03 s) 4#usize 512#usize 6922#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 512 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 480 v03
      6922#u32 3#usize (encodeState value027) 512#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 7982#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 512 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value016) :=
    JGm_TX2_View.value (s04 s) indices04 values04 512 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=512#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠7982#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨16544#u32,JGm_TX2_View.index (s04 s) indices04 values04 512 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s04 s).«at» 544#usize)=ok (encodeState (JGc_TX2_HashBytes.state [233,12,76,182,55,86,131,28,134,104,64,245,5,248,85,26,112,218,240,222,87,201,63,197,143,161,1,205,152,1,87,146])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 16
      4512#usize 512#usize 544#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings01.k2c016_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes2 4#usize 4#usize 5#usize 544#usize 4000#usize
    7982#u32 (encodeState value016) (encodeState (JGc_TX2_HashBytes.state [233,12,76,182,55,86,131,28,134,104,64,245,5,248,85,26,112,218,240,222,87,201,63,197,143,161,1,205,152,1,87,146])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read04
  simp only [show 7982#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes2 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls2.source028 D hash (s04 s) 5#usize 544#usize 7982#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 544 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 512 v04
      7982#u32 4#usize (encodeState value028) 544#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 16544#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 544 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value017) :=
    JGm_TX2_View.value (s05 s) indices05 values05 544 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=544#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠16544#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨18703#u32,JGm_TX2_View.index (s05 s) indices05 values05 544 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s05 s).«at» 576#usize)=ok (encodeState (JGc_TX2_HashBytes.state [41,123,146,98,74,41,194,48,129,190,154,231,228,83,190,152,113,0,84,3,82,78,64,108,73,103,48,204,39,90,128,180])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 17
      4512#usize 544#usize 576#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings01.k2c017_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes2 5#usize 5#usize 6#usize 576#usize 3968#usize
    16544#u32 (encodeState value017) (encodeState (JGc_TX2_HashBytes.state [41,123,146,98,74,41,194,48,129,190,154,231,228,83,190,152,113,0,84,3,82,78,64,108,73,103,48,204,39,90,128,180])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read05
  simp only [show 16544#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes2 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls2.source029 D hash (s05 s) 6#usize 576#usize 16544#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 576 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 544 v05
      16544#u32 5#usize (encodeState value029) 576#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 18703#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 576 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value018) :=
    JGm_TX2_View.value (s06 s) indices06 values06 576 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=576#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠18703#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨20770#u32,JGm_TX2_View.index (s06 s) indices06 values06 576 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s06 s).«at» 608#usize)=ok (encodeState (JGc_TX2_HashBytes.state [197,218,140,229,49,134,37,57,194,185,240,206,239,92,48,217,156,44,145,139,116,206,138,85,253,224,195,206,148,79,137,249])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 18
      4512#usize 576#usize 608#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings01.k2c018_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes2 6#usize 6#usize 7#usize 608#usize 3936#usize
    18703#u32 (encodeState value018) (encodeState (JGc_TX2_HashBytes.state [197,218,140,229,49,134,37,57,194,185,240,206,239,92,48,217,156,44,145,139,116,206,138,85,253,224,195,206,148,79,137,249])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read06
  simp only [show 18703#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes2 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls2.source030 D hash (s06 s) 7#usize 608#usize 18703#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 608 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 576 v06
      18703#u32 6#usize (encodeState value030) 608#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 20770#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 608 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value019) :=
    JGm_TX2_View.value (s07 s) indices07 values07 608 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=608#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠20770#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨22260#u32,JGm_TX2_View.index (s07 s) indices07 values07 608 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s07 s).«at» 640#usize)=ok (encodeState (JGc_TX2_HashBytes.state [178,0,87,176,242,109,72,47,236,219,104,45,218,234,49,125,20,64,147,191,238,235,142,180,71,229,234,13,235,62,31,222])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 19
      4512#usize 608#usize 640#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings01.k2c019_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes2 7#usize 7#usize 8#usize 640#usize 3904#usize
    20770#u32 (encodeState value019) (encodeState (JGc_TX2_HashBytes.state [178,0,87,176,242,109,72,47,236,219,104,45,218,234,49,125,20,64,147,191,238,235,142,180,71,229,234,13,235,62,31,222])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read07
  simp only [show 20770#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes2 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls2.source031 D hash (s07 s) 8#usize 640#usize 20770#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 640 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 608 v07
      20770#u32 7#usize (encodeState value031) 640#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 22260#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 640 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value020) :=
    JGm_TX2_View.value (s08 s) indices08 values08 640 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=640#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠22260#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨22452#u32,JGm_TX2_View.index (s08 s) indices08 values08 640 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s08 s).«at» 672#usize)=ok (encodeState (JGc_TX2_HashBytes.state [83,160,147,101,157,27,33,159,100,90,115,0,45,96,6,225,224,46,153,6,49,103,54,140,125,129,85,191,42,2,132,189])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 20
      4512#usize 640#usize 672#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings01.k2c020_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes2 8#usize 8#usize 9#usize 672#usize 3872#usize
    22260#u32 (encodeState value020) (encodeState (JGc_TX2_HashBytes.state [83,160,147,101,157,27,33,159,100,90,115,0,45,96,6,225,224,46,153,6,49,103,54,140,125,129,85,191,42,2,132,189])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read08
  simp only [show 22260#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes2 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls2.source032 D hash (s08 s) 9#usize 672#usize 22260#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 672 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 640 v08
      22260#u32 8#usize (encodeState value032) 672#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 22452#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 672 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value021) :=
    JGm_TX2_View.value (s09 s) indices09 values09 672 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=672#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠22452#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨23204#u32,JGm_TX2_View.index (s09 s) indices09 values09 672 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s09 s).«at» 704#usize)=ok (encodeState (JGc_TX2_HashBytes.state [153,19,7,14,39,146,75,143,167,19,170,143,26,60,63,207,209,103,140,223,4,181,82,97,131,224,162,105,220,45,101,229])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 21
      4512#usize 672#usize 704#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings01.k2c021_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes2 9#usize 9#usize 10#usize 704#usize 3840#usize
    22452#u32 (encodeState value021) (encodeState (JGc_TX2_HashBytes.state [153,19,7,14,39,146,75,143,167,19,170,143,26,60,63,207,209,103,140,223,4,181,82,97,131,224,162,105,220,45,101,229])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read09
  simp only [show 22452#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes2 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls2.source033 D hash (s09 s) 10#usize 704#usize 22452#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 704 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 672 v09
      22452#u32 9#usize (encodeState value033) 704#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 23204#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 704 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value022) :=
    JGm_TX2_View.value (s10 s) indices10 values10 704 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=704#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠23204#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨27261#u32,JGm_TX2_View.index (s10 s) indices10 values10 704 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s10 s).«at» 736#usize)=ok (encodeState (JGc_TX2_HashBytes.state [149,146,136,206,135,184,54,243,49,151,144,138,183,57,96,167,205,119,38,18,59,15,214,146,121,90,119,232,157,129,235,177])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 22
      4512#usize 704#usize 736#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings01.k2c022_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes2 10#usize 10#usize 11#usize 736#usize 3808#usize
    23204#u32 (encodeState value022) (encodeState (JGc_TX2_HashBytes.state [149,146,136,206,135,184,54,243,49,151,144,138,183,57,96,167,205,119,38,18,59,15,214,146,121,90,119,232,157,129,235,177])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read10
  simp only [show 23204#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes2 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls2.source034 D hash (s10 s) 11#usize 736#usize 23204#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 736 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 704 v10
      23204#u32 10#usize (encodeState value034) 736#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 27261#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 736 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value023) :=
    JGm_TX2_View.value (s11 s) indices11 values11 736 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=736#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠27261#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s11 s).«at» 768#usize)=ok (encodeState (JGc_TX2_HashBytes.state [10,30,26,104,25,237,52,75,60,229,159,181,23,252,33,103,235,23,37,234,195,95,102,113,140,111,81,254,244,220,95,33])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 23
      4512#usize 736#usize 768#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings01.k2c023_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes2 11#usize 11#usize 12#usize 768#usize 3776#usize
    27261#u32 (encodeState value023) (encodeState (JGc_TX2_HashBytes.state [10,30,26,104,25,237,52,75,60,229,159,181,23,252,33,103,235,23,37,234,195,95,102,113,140,111,81,254,244,220,95,33])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read11
  simp only [show 27261#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes2 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls2.source035 D hash (s11 s) 12#usize 768#usize 27261#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 768 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 736 v11
      27261#u32 11#usize (encodeState value035) 768#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGm_TX2_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGm_TX2_Supplied.nodes2 1#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGm_TX2_Supplied.nodes2 2#usize 2#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGm_TX2_Supplied.nodes2 3#usize 3#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGm_TX2_Supplied.nodes2 4#usize 4#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGm_TX2_Supplied.nodes2 5#usize 5#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGm_TX2_Supplied.nodes2 6#usize 6#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGm_TX2_Supplied.nodes2 7#usize 7#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGm_TX2_Supplied.nodes2 8#usize 8#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGm_TX2_Supplied.nodes2 9#usize 9#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGm_TX2_Supplied.nodes2 10#usize 10#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s) JGm_TX2_Supplied.nodes2 11#usize 11#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active10 row10
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s12 s) JGm_TX2_Supplied.nodes2 12#usize 12#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active11 row11
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s12 s).n.val≤12;rw [v12.size];decide)
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 768
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level2_01
end
