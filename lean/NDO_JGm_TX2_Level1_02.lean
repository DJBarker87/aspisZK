import NDO_JGm_TX2_ParentCalls1
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level1_02
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGh_TX2_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes1
def indices00 : List U32 := [3574#u32,5312#u32,10539#u32,13844#u32,15965#u32,33088#u32,37406#u32,41541#u32,44520#u32,44905#u32,46409#u32,54523#u32]
def values00 : List (Array U8 32#usize) := [encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 3574#u32 0#usize (encodeState value036) 800#usize
 def indices01 : List U32 := [1787#u32,5312#u32,10539#u32,13844#u32,15965#u32,33088#u32,37406#u32,41541#u32,44520#u32,44905#u32,46409#u32,54523#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value036,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 5312#u32 1#usize (encodeState value037) 832#usize
 def indices02 : List U32 := [1787#u32,2656#u32,10539#u32,13844#u32,15965#u32,33088#u32,37406#u32,41541#u32,44520#u32,44905#u32,46409#u32,54523#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value026,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 10539#u32 2#usize (encodeState value038) 864#usize
 def indices03 : List U32 := [1787#u32,2656#u32,5269#u32,13844#u32,15965#u32,33088#u32,37406#u32,41541#u32,44520#u32,44905#u32,46409#u32,54523#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 13844#u32 3#usize (encodeState value039) 896#usize
 def indices04 : List U32 := [1787#u32,2656#u32,5269#u32,6922#u32,15965#u32,33088#u32,37406#u32,41541#u32,44520#u32,44905#u32,46409#u32,54523#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 15965#u32 4#usize (encodeState value040) 928#usize
 def indices05 : List U32 := [1787#u32,2656#u32,5269#u32,6922#u32,7982#u32,33088#u32,37406#u32,41541#u32,44520#u32,44905#u32,46409#u32,54523#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 33088#u32 5#usize (encodeState value041) 960#usize
 def indices06 : List U32 := [1787#u32,2656#u32,5269#u32,6922#u32,7982#u32,16544#u32,37406#u32,41541#u32,44520#u32,44905#u32,46409#u32,54523#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 37406#u32 6#usize (encodeState value042) 992#usize
 def indices07 : List U32 := [1787#u32,2656#u32,5269#u32,6922#u32,7982#u32,16544#u32,18703#u32,41541#u32,44520#u32,44905#u32,46409#u32,54523#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 41541#u32 7#usize (encodeState value043) 1024#usize
 def indices08 : List U32 := [1787#u32,2656#u32,5269#u32,6922#u32,7982#u32,16544#u32,18703#u32,20770#u32,44520#u32,44905#u32,46409#u32,54523#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 44520#u32 8#usize (encodeState value044) 1056#usize
 def indices09 : List U32 := [1787#u32,2656#u32,5269#u32,6922#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,44905#u32,46409#u32,54523#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value033,encodeState value034,encodeState value035]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 44905#u32 9#usize (encodeState value045) 1088#usize
 def indices10 : List U32 := [1787#u32,2656#u32,5269#u32,6922#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,46409#u32,54523#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value034,encodeState value035]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 46409#u32 10#usize (encodeState value046) 1120#usize
 def indices11 : List U32 := [1787#u32,2656#u32,5269#u32,6922#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,54523#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value035]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 54523#u32 11#usize (encodeState value047) 1152#usize
 def indices12 : List U32 := [1787#u32,2656#u32,5269#u32,6922#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [1787#u32,2656#u32,5269#u32,6922#u32,7982#u32,16544#u32,18703#u32,20770#u32,22260#u32,22452#u32,23204#u32,27261#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 768) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 1152 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 768 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 3574#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 768 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value024) :=
    JGm_TX2_View.value (s00 s) indices00 values00 768 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=768#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠3574#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨5312#u32,JGm_TX2_View.index (s00 s) indices00 values00 768 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s00 s).«at» 800#usize)=ok (encodeState (JGc_TX2_HashBytes.state [97,127,45,224,226,170,233,49,234,134,73,253,142,237,10,38,127,193,71,183,230,237,164,189,249,186,117,212,49,152,176,19])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 24
      5216#usize 768#usize 800#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings02.k1c024_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes1 0#usize 0#usize 1#usize 800#usize 4448#usize
    3574#u32 (encodeState value024) (encodeState (JGc_TX2_HashBytes.state [97,127,45,224,226,170,233,49,234,134,73,253,142,237,10,38,127,193,71,183,230,237,164,189,249,186,117,212,49,152,176,19])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read00
  simp only [show 3574#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls1.source036 D hash (s00 s) 1#usize 800#usize 3574#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 800 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 768 v00
      3574#u32 0#usize (encodeState value036) 800#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 5312#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 800 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value025) :=
    JGm_TX2_View.value (s01 s) indices01 values01 800 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=800#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠5312#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨10539#u32,JGm_TX2_View.index (s01 s) indices01 values01 800 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s01 s).«at» 832#usize)=ok (encodeState (JGc_TX2_HashBytes.state [55,134,167,154,32,84,223,159,219,123,45,8,206,182,36,8,143,2,22,155,30,49,237,73,95,111,245,167,63,236,244,215])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 25
      5216#usize 800#usize 832#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings02.k1c025_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes1 1#usize 1#usize 2#usize 832#usize 4416#usize
    5312#u32 (encodeState value025) (encodeState (JGc_TX2_HashBytes.state [55,134,167,154,32,84,223,159,219,123,45,8,206,182,36,8,143,2,22,155,30,49,237,73,95,111,245,167,63,236,244,215])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read01
  simp only [show 5312#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls1.source037 D hash (s01 s) 2#usize 832#usize 5312#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 832 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 800 v01
      5312#u32 1#usize (encodeState value037) 832#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 10539#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 832 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value026) :=
    JGm_TX2_View.value (s02 s) indices02 values02 832 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=832#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠10539#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨13844#u32,JGm_TX2_View.index (s02 s) indices02 values02 832 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s02 s).«at» 864#usize)=ok (encodeState (JGc_TX2_HashBytes.state [64,2,44,46,241,45,160,34,120,196,208,37,152,255,204,191,252,202,201,221,153,96,198,26,94,15,113,122,33,88,64,28])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 26
      5216#usize 832#usize 864#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings02.k1c026_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes1 2#usize 2#usize 3#usize 864#usize 4384#usize
    10539#u32 (encodeState value026) (encodeState (JGc_TX2_HashBytes.state [64,2,44,46,241,45,160,34,120,196,208,37,152,255,204,191,252,202,201,221,153,96,198,26,94,15,113,122,33,88,64,28])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read02
  simp only [show 10539#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls1.source038 D hash (s02 s) 3#usize 864#usize 10539#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 864 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 832 v02
      10539#u32 2#usize (encodeState value038) 864#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 13844#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 864 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value027) :=
    JGm_TX2_View.value (s03 s) indices03 values03 864 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=864#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠13844#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨15965#u32,JGm_TX2_View.index (s03 s) indices03 values03 864 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s03 s).«at» 896#usize)=ok (encodeState (JGc_TX2_HashBytes.state [94,143,135,120,251,114,163,154,6,3,87,192,188,32,202,66,233,97,109,140,6,215,197,145,60,155,46,91,223,31,174,88])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 27
      5216#usize 864#usize 896#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings02.k1c027_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes1 3#usize 3#usize 4#usize 896#usize 4352#usize
    13844#u32 (encodeState value027) (encodeState (JGc_TX2_HashBytes.state [94,143,135,120,251,114,163,154,6,3,87,192,188,32,202,66,233,97,109,140,6,215,197,145,60,155,46,91,223,31,174,88])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read03
  simp only [show 13844#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls1.source039 D hash (s03 s) 4#usize 896#usize 13844#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 896 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 864 v03
      13844#u32 3#usize (encodeState value039) 896#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 15965#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 896 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value028) :=
    JGm_TX2_View.value (s04 s) indices04 values04 896 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=896#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠15965#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨33088#u32,JGm_TX2_View.index (s04 s) indices04 values04 896 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s04 s).«at» 928#usize)=ok (encodeState (JGc_TX2_HashBytes.state [166,240,188,205,87,246,220,78,119,242,202,113,95,112,228,101,111,124,44,88,53,182,231,191,10,212,92,239,228,176,66,74])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 28
      5216#usize 896#usize 928#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings02.k1c028_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes1 4#usize 4#usize 5#usize 928#usize 4320#usize
    15965#u32 (encodeState value028) (encodeState (JGc_TX2_HashBytes.state [166,240,188,205,87,246,220,78,119,242,202,113,95,112,228,101,111,124,44,88,53,182,231,191,10,212,92,239,228,176,66,74])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read04
  simp only [show 15965#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls1.source040 D hash (s04 s) 5#usize 928#usize 15965#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 928 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 896 v04
      15965#u32 4#usize (encodeState value040) 928#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 33088#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 928 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value029) :=
    JGm_TX2_View.value (s05 s) indices05 values05 928 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=928#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠33088#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨37406#u32,JGm_TX2_View.index (s05 s) indices05 values05 928 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s05 s).«at» 960#usize)=ok (encodeState (JGc_TX2_HashBytes.state [50,110,138,55,85,52,37,101,181,66,44,4,215,27,106,50,145,156,227,241,190,145,73,161,14,84,188,105,217,219,70,28])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 29
      5216#usize 928#usize 960#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings02.k1c029_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes1 5#usize 5#usize 6#usize 960#usize 4288#usize
    33088#u32 (encodeState value029) (encodeState (JGc_TX2_HashBytes.state [50,110,138,55,85,52,37,101,181,66,44,4,215,27,106,50,145,156,227,241,190,145,73,161,14,84,188,105,217,219,70,28])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read05
  simp only [show 33088#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls1.source041 D hash (s05 s) 6#usize 960#usize 33088#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 960 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 928 v05
      33088#u32 5#usize (encodeState value041) 960#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 37406#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 960 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value030) :=
    JGm_TX2_View.value (s06 s) indices06 values06 960 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=960#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠37406#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨41541#u32,JGm_TX2_View.index (s06 s) indices06 values06 960 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s06 s).«at» 992#usize)=ok (encodeState (JGc_TX2_HashBytes.state [2,179,245,189,108,52,207,91,132,34,120,104,44,35,237,157,117,47,189,147,220,3,126,153,141,11,193,62,160,114,102,191])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 30
      5216#usize 960#usize 992#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings02.k1c030_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes1 6#usize 6#usize 7#usize 992#usize 4256#usize
    37406#u32 (encodeState value030) (encodeState (JGc_TX2_HashBytes.state [2,179,245,189,108,52,207,91,132,34,120,104,44,35,237,157,117,47,189,147,220,3,126,153,141,11,193,62,160,114,102,191])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read06
  simp only [show 37406#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls1.source042 D hash (s06 s) 7#usize 992#usize 37406#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 992 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 960 v06
      37406#u32 6#usize (encodeState value042) 992#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 41541#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 992 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value031) :=
    JGm_TX2_View.value (s07 s) indices07 values07 992 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=992#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠41541#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨44520#u32,JGm_TX2_View.index (s07 s) indices07 values07 992 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s07 s).«at» 1024#usize)=ok (encodeState (JGc_TX2_HashBytes.state [53,114,132,46,186,166,92,88,104,211,173,253,87,181,205,236,11,203,144,188,40,230,240,23,98,232,115,106,226,28,201,184])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 31
      5216#usize 992#usize 1024#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings02.k1c031_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes1 7#usize 7#usize 8#usize 1024#usize 4224#usize
    41541#u32 (encodeState value031) (encodeState (JGc_TX2_HashBytes.state [53,114,132,46,186,166,92,88,104,211,173,253,87,181,205,236,11,203,144,188,40,230,240,23,98,232,115,106,226,28,201,184])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read07
  simp only [show 41541#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls1.source043 D hash (s07 s) 8#usize 1024#usize 41541#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 1024 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 992 v07
      41541#u32 7#usize (encodeState value043) 1024#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 44520#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 1024 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value032) :=
    JGm_TX2_View.value (s08 s) indices08 values08 1024 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=1024#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠44520#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨44905#u32,JGm_TX2_View.index (s08 s) indices08 values08 1024 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s08 s).«at» 1056#usize)=ok (encodeState (JGc_TX2_HashBytes.state [113,112,35,231,139,214,179,119,132,123,176,214,78,91,93,17,20,254,88,184,85,103,68,48,232,61,247,103,196,246,43,235])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 32
      5216#usize 1024#usize 1056#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings02.k1c032_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes1 8#usize 8#usize 9#usize 1056#usize 4192#usize
    44520#u32 (encodeState value032) (encodeState (JGc_TX2_HashBytes.state [113,112,35,231,139,214,179,119,132,123,176,214,78,91,93,17,20,254,88,184,85,103,68,48,232,61,247,103,196,246,43,235])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read08
  simp only [show 44520#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls1.source044 D hash (s08 s) 9#usize 1056#usize 44520#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 1056 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 1024 v08
      44520#u32 8#usize (encodeState value044) 1056#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 44905#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 1056 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value033) :=
    JGm_TX2_View.value (s09 s) indices09 values09 1056 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=1056#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠44905#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨46409#u32,JGm_TX2_View.index (s09 s) indices09 values09 1056 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s09 s).«at» 1088#usize)=ok (encodeState (JGc_TX2_HashBytes.state [129,72,67,82,242,126,71,182,192,27,62,249,25,188,16,252,234,20,43,168,77,243,60,144,123,206,201,85,74,108,95,91])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 33
      5216#usize 1056#usize 1088#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings02.k1c033_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes1 9#usize 9#usize 10#usize 1088#usize 4160#usize
    44905#u32 (encodeState value033) (encodeState (JGc_TX2_HashBytes.state [129,72,67,82,242,126,71,182,192,27,62,249,25,188,16,252,234,20,43,168,77,243,60,144,123,206,201,85,74,108,95,91])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read09
  simp only [show 44905#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls1.source045 D hash (s09 s) 10#usize 1088#usize 44905#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 1088 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 1056 v09
      44905#u32 9#usize (encodeState value045) 1088#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 46409#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 1088 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value034) :=
    JGm_TX2_View.value (s10 s) indices10 values10 1088 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=1088#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠46409#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨54523#u32,JGm_TX2_View.index (s10 s) indices10 values10 1088 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s10 s).«at» 1120#usize)=ok (encodeState (JGc_TX2_HashBytes.state [6,37,171,139,92,51,101,71,160,15,26,2,216,90,109,219,223,194,156,101,196,87,158,89,191,69,44,129,248,130,247,70])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 34
      5216#usize 1088#usize 1120#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings02.k1c034_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes1 10#usize 10#usize 11#usize 1120#usize 4128#usize
    46409#u32 (encodeState value034) (encodeState (JGc_TX2_HashBytes.state [6,37,171,139,92,51,101,71,160,15,26,2,216,90,109,219,223,194,156,101,196,87,158,89,191,69,44,129,248,130,247,70])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read10
  simp only [show 46409#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes1 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls1.source046 D hash (s10 s) 11#usize 1120#usize 46409#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 1120 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 1088 v10
      46409#u32 10#usize (encodeState value046) 1120#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 54523#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 1120 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value035) :=
    JGm_TX2_View.value (s11 s) indices11 values11 1120 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=1120#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠54523#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s11 s).«at» 1152#usize)=ok (encodeState (JGc_TX2_HashBytes.state [68,157,45,113,195,182,5,150,228,230,64,164,162,241,47,246,114,48,101,22,44,185,35,111,36,40,34,61,67,79,45,201])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 35
      5216#usize 1120#usize 1152#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings02.k1c035_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes1 11#usize 11#usize 12#usize 1152#usize 4096#usize
    54523#u32 (encodeState value035) (encodeState (JGc_TX2_HashBytes.state [68,157,45,113,195,182,5,150,228,230,64,164,162,241,47,246,114,48,101,22,44,185,35,111,36,40,34,61,67,79,45,201])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read11
  simp only [show 54523#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes1 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls1.source047 D hash (s11 s) 12#usize 1152#usize 54523#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 1152 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 1120 v11
      54523#u32 11#usize (encodeState value047) 1152#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 1152
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level1_02
end
