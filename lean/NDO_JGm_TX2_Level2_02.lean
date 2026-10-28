import NDO_JGm_TX2_ParentCalls2
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level2_02
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGc_TX2_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes2
def indices00 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
def values00 : List (Array U8 32#usize) := [encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 893#u32 0#usize (encodeState value036) 800#usize
 def indices01 : List U32 := [446#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value036,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 1328#u32 1#usize (encodeState value037) 832#usize
 def indices02 : List U32 := [446#u32,664#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value026,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 2634#u32 2#usize (encodeState value038) 864#usize
 def indices03 : List U32 := [446#u32,664#u32,1317#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value027,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 3461#u32 3#usize (encodeState value039) 896#usize
 def indices04 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value028,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 3991#u32 4#usize (encodeState value040) 928#usize
 def indices05 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value029,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 8272#u32 5#usize (encodeState value041) 960#usize
 def indices06 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 9351#u32 6#usize (encodeState value042) 992#usize
 def indices07 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 10385#u32 7#usize (encodeState value043) 1024#usize
 def indices08 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value032,encodeState value033,encodeState value034,encodeState value035]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 11130#u32 8#usize (encodeState value044) 1056#usize
 def indices09 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,11226#u32,11602#u32,13630#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value033,encodeState value034,encodeState value035]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 11226#u32 9#usize (encodeState value045) 1088#usize
 def indices10 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,5613#u32,11602#u32,13630#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value034,encodeState value035]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 11602#u32 10#usize (encodeState value046) 1120#usize
 def indices11 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,5613#u32,5801#u32,13630#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value035]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 13630#u32 11#usize (encodeState value047) 1152#usize
 def indices12 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,5613#u32,5801#u32,6815#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,5613#u32,5801#u32,6815#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value036,encodeState value037,encodeState value038,encodeState value039,encodeState value040,encodeState value041,encodeState value042,encodeState value043,encodeState value044,encodeState value045,encodeState value046,encodeState value047]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 768) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 1152 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 768 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 893#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 768 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value024) :=
    JGm_TX2_View.value (s00 s) indices00 values00 768 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=768#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠893#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1328#u32,JGm_TX2_View.index (s00 s) indices00 values00 768 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s00 s).«at» 800#usize)=ok (encodeState (JGc_TX2_HashBytes.state [142,71,54,188,107,133,110,82,78,24,73,35,118,78,156,74,51,2,8,253,198,10,145,101,147,12,247,219,22,143,114,74])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 24
      4512#usize 768#usize 800#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings02.k2c024_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes2 0#usize 0#usize 1#usize 800#usize 3744#usize
    893#u32 (encodeState value024) (encodeState (JGc_TX2_HashBytes.state [142,71,54,188,107,133,110,82,78,24,73,35,118,78,156,74,51,2,8,253,198,10,145,101,147,12,247,219,22,143,114,74])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read00
  simp only [show 893#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls2.source036 D hash (s00 s) 1#usize 800#usize 893#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 800 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 768 v00
      893#u32 0#usize (encodeState value036) 800#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 1328#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 800 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value025) :=
    JGm_TX2_View.value (s01 s) indices01 values01 800 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=800#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠1328#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2634#u32,JGm_TX2_View.index (s01 s) indices01 values01 800 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s01 s).«at» 832#usize)=ok (encodeState (JGc_TX2_HashBytes.state [74,30,88,56,127,42,19,72,31,188,143,39,106,80,217,195,93,172,40,241,251,138,112,28,199,224,139,49,101,237,114,234])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 25
      4512#usize 800#usize 832#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings02.k2c025_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes2 1#usize 1#usize 2#usize 832#usize 3712#usize
    1328#u32 (encodeState value025) (encodeState (JGc_TX2_HashBytes.state [74,30,88,56,127,42,19,72,31,188,143,39,106,80,217,195,93,172,40,241,251,138,112,28,199,224,139,49,101,237,114,234])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read01
  simp only [show 1328#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls2.source037 D hash (s01 s) 2#usize 832#usize 1328#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 832 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 800 v01
      1328#u32 1#usize (encodeState value037) 832#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 2634#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 832 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value026) :=
    JGm_TX2_View.value (s02 s) indices02 values02 832 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=832#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠2634#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3461#u32,JGm_TX2_View.index (s02 s) indices02 values02 832 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s02 s).«at» 864#usize)=ok (encodeState (JGc_TX2_HashBytes.state [206,11,178,87,46,111,7,245,239,183,26,116,42,155,14,231,45,73,139,243,181,182,22,57,169,101,81,27,133,115,213,188])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 26
      4512#usize 832#usize 864#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings02.k2c026_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes2 2#usize 2#usize 3#usize 864#usize 3680#usize
    2634#u32 (encodeState value026) (encodeState (JGc_TX2_HashBytes.state [206,11,178,87,46,111,7,245,239,183,26,116,42,155,14,231,45,73,139,243,181,182,22,57,169,101,81,27,133,115,213,188])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read02
  simp only [show 2634#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls2.source038 D hash (s02 s) 3#usize 864#usize 2634#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 864 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 832 v02
      2634#u32 2#usize (encodeState value038) 864#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 3461#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 864 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value027) :=
    JGm_TX2_View.value (s03 s) indices03 values03 864 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=864#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠3461#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3991#u32,JGm_TX2_View.index (s03 s) indices03 values03 864 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s03 s).«at» 896#usize)=ok (encodeState (JGc_TX2_HashBytes.state [156,227,32,66,1,53,116,61,225,43,126,205,31,159,50,40,201,176,218,21,156,174,60,26,165,45,21,219,171,1,178,128])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 27
      4512#usize 864#usize 896#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings02.k2c027_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes2 3#usize 3#usize 4#usize 896#usize 3648#usize
    3461#u32 (encodeState value027) (encodeState (JGc_TX2_HashBytes.state [156,227,32,66,1,53,116,61,225,43,126,205,31,159,50,40,201,176,218,21,156,174,60,26,165,45,21,219,171,1,178,128])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read03
  simp only [show 3461#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes2 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls2.source039 D hash (s03 s) 4#usize 896#usize 3461#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 896 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 864 v03
      3461#u32 3#usize (encodeState value039) 896#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 3991#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 896 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value028) :=
    JGm_TX2_View.value (s04 s) indices04 values04 896 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=896#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠3991#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨8272#u32,JGm_TX2_View.index (s04 s) indices04 values04 896 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s04 s).«at» 928#usize)=ok (encodeState (JGc_TX2_HashBytes.state [203,230,190,57,102,61,126,184,252,81,69,36,204,93,127,113,125,96,51,17,206,230,4,207,149,49,250,81,52,72,1,82])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 28
      4512#usize 896#usize 928#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings02.k2c028_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes2 4#usize 4#usize 5#usize 928#usize 3616#usize
    3991#u32 (encodeState value028) (encodeState (JGc_TX2_HashBytes.state [203,230,190,57,102,61,126,184,252,81,69,36,204,93,127,113,125,96,51,17,206,230,4,207,149,49,250,81,52,72,1,82])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read04
  simp only [show 3991#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes2 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls2.source040 D hash (s04 s) 5#usize 928#usize 3991#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 928 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 896 v04
      3991#u32 4#usize (encodeState value040) 928#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 8272#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 928 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value029) :=
    JGm_TX2_View.value (s05 s) indices05 values05 928 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=928#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠8272#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨9351#u32,JGm_TX2_View.index (s05 s) indices05 values05 928 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s05 s).«at» 960#usize)=ok (encodeState (JGc_TX2_HashBytes.state [120,163,23,75,229,163,190,245,25,235,189,36,155,129,116,31,246,96,195,137,212,238,94,152,43,249,59,40,204,149,245,225])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 29
      4512#usize 928#usize 960#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings02.k2c029_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes2 5#usize 5#usize 6#usize 960#usize 3584#usize
    8272#u32 (encodeState value029) (encodeState (JGc_TX2_HashBytes.state [120,163,23,75,229,163,190,245,25,235,189,36,155,129,116,31,246,96,195,137,212,238,94,152,43,249,59,40,204,149,245,225])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read05
  simp only [show 8272#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes2 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls2.source041 D hash (s05 s) 6#usize 960#usize 8272#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 960 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 928 v05
      8272#u32 5#usize (encodeState value041) 960#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 9351#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 960 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value030) :=
    JGm_TX2_View.value (s06 s) indices06 values06 960 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=960#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠9351#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨10385#u32,JGm_TX2_View.index (s06 s) indices06 values06 960 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s06 s).«at» 992#usize)=ok (encodeState (JGc_TX2_HashBytes.state [14,28,34,57,248,175,178,171,228,145,45,180,7,239,120,13,208,166,227,58,25,179,76,71,40,183,89,53,119,141,253,147])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 30
      4512#usize 960#usize 992#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings02.k2c030_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes2 6#usize 6#usize 7#usize 992#usize 3552#usize
    9351#u32 (encodeState value030) (encodeState (JGc_TX2_HashBytes.state [14,28,34,57,248,175,178,171,228,145,45,180,7,239,120,13,208,166,227,58,25,179,76,71,40,183,89,53,119,141,253,147])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read06
  simp only [show 9351#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes2 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls2.source042 D hash (s06 s) 7#usize 992#usize 9351#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 992 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 960 v06
      9351#u32 6#usize (encodeState value042) 992#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 10385#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 992 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value031) :=
    JGm_TX2_View.value (s07 s) indices07 values07 992 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=992#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠10385#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨11130#u32,JGm_TX2_View.index (s07 s) indices07 values07 992 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s07 s).«at» 1024#usize)=ok (encodeState (JGc_TX2_HashBytes.state [178,62,234,178,9,104,69,132,134,195,173,184,104,113,115,99,58,180,164,232,36,99,7,108,99,193,68,245,243,39,190,128])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 31
      4512#usize 992#usize 1024#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings02.k2c031_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes2 7#usize 7#usize 8#usize 1024#usize 3520#usize
    10385#u32 (encodeState value031) (encodeState (JGc_TX2_HashBytes.state [178,62,234,178,9,104,69,132,134,195,173,184,104,113,115,99,58,180,164,232,36,99,7,108,99,193,68,245,243,39,190,128])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read07
  simp only [show 10385#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes2 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls2.source043 D hash (s07 s) 8#usize 1024#usize 10385#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 1024 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 992 v07
      10385#u32 7#usize (encodeState value043) 1024#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 11130#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 1024 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value032) :=
    JGm_TX2_View.value (s08 s) indices08 values08 1024 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=1024#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠11130#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨11226#u32,JGm_TX2_View.index (s08 s) indices08 values08 1024 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s08 s).«at» 1056#usize)=ok (encodeState (JGc_TX2_HashBytes.state [221,48,192,214,43,179,218,136,161,122,96,85,118,17,76,248,85,214,125,182,28,105,218,151,59,182,71,42,135,79,183,244])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 32
      4512#usize 1024#usize 1056#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings02.k2c032_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes2 8#usize 8#usize 9#usize 1056#usize 3488#usize
    11130#u32 (encodeState value032) (encodeState (JGc_TX2_HashBytes.state [221,48,192,214,43,179,218,136,161,122,96,85,118,17,76,248,85,214,125,182,28,105,218,151,59,182,71,42,135,79,183,244])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read08
  simp only [show 11130#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes2 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls2.source044 D hash (s08 s) 9#usize 1056#usize 11130#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 1056 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 1024 v08
      11130#u32 8#usize (encodeState value044) 1056#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 11226#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 1056 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value033) :=
    JGm_TX2_View.value (s09 s) indices09 values09 1056 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=1056#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠11226#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨11602#u32,JGm_TX2_View.index (s09 s) indices09 values09 1056 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s09 s).«at» 1088#usize)=ok (encodeState (JGc_TX2_HashBytes.state [217,198,135,10,247,252,247,246,146,73,29,244,198,43,86,74,43,7,122,190,168,254,172,72,101,127,251,76,155,109,142,243])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 33
      4512#usize 1056#usize 1088#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings02.k2c033_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes2 9#usize 9#usize 10#usize 1088#usize 3456#usize
    11226#u32 (encodeState value033) (encodeState (JGc_TX2_HashBytes.state [217,198,135,10,247,252,247,246,146,73,29,244,198,43,86,74,43,7,122,190,168,254,172,72,101,127,251,76,155,109,142,243])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read09
  simp only [show 11226#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes2 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls2.source045 D hash (s09 s) 10#usize 1088#usize 11226#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 1088 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 1056 v09
      11226#u32 9#usize (encodeState value045) 1088#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 11602#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 1088 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value034) :=
    JGm_TX2_View.value (s10 s) indices10 values10 1088 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=1088#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠11602#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨13630#u32,JGm_TX2_View.index (s10 s) indices10 values10 1088 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s10 s).«at» 1120#usize)=ok (encodeState (JGc_TX2_HashBytes.state [109,115,192,31,41,81,198,223,206,2,158,136,206,203,255,61,129,211,85,123,147,41,151,174,213,209,220,252,211,163,108,220])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 34
      4512#usize 1088#usize 1120#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings02.k2c034_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes2 10#usize 10#usize 11#usize 1120#usize 3424#usize
    11602#u32 (encodeState value034) (encodeState (JGc_TX2_HashBytes.state [109,115,192,31,41,81,198,223,206,2,158,136,206,203,255,61,129,211,85,123,147,41,151,174,213,209,220,252,211,163,108,220])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read10
  simp only [show 11602#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes2 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls2.source046 D hash (s10 s) 11#usize 1120#usize 11602#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 1120 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 1088 v10
      11602#u32 10#usize (encodeState value046) 1120#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 13630#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 1120 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value035) :=
    JGm_TX2_View.value (s11 s) indices11 values11 1120 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=1120#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠13630#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s11 s).«at» 1152#usize)=ok (encodeState (JGc_TX2_HashBytes.state [29,225,72,200,54,205,19,189,140,62,230,165,80,225,188,225,255,120,73,38,198,94,209,252,38,156,219,161,245,119,125,66])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 35
      4512#usize 1120#usize 1152#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings02.k2c035_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes2 11#usize 11#usize 12#usize 1152#usize 3392#usize
    13630#u32 (encodeState value035) (encodeState (JGc_TX2_HashBytes.state [29,225,72,200,54,205,19,189,140,62,230,165,80,225,188,225,255,120,73,38,198,94,209,252,38,156,219,161,245,119,125,66])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read11
  simp only [show 13630#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes2 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls2.source047 D hash (s11 s) 12#usize 1152#usize 13630#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 1152 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 1120 v11
      13630#u32 11#usize (encodeState value047) 1152#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 1152
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level2_02
end
