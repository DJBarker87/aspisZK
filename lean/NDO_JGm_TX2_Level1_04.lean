import NDO_JGm_TX2_ParentCalls1
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level1_04
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGh_TX2_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes1
def indices00 : List U32 := [893#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
def values00 : List (Array U8 32#usize) := [encodeState value048,encodeState value049,encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 893#u32 0#usize (encodeState value060) 1568#usize
 def indices01 : List U32 := [446#u32,1328#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value060,encodeState value049,encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 1328#u32 1#usize (encodeState value061) 1600#usize
 def indices02 : List U32 := [446#u32,664#u32,2634#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 2634#u32 2#usize (encodeState value062) 1632#usize
 def indices03 : List U32 := [446#u32,664#u32,1317#u32,3461#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 3461#u32 3#usize (encodeState value063) 1664#usize
 def indices04 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,3991#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 3991#u32 4#usize (encodeState value064) 1696#usize
 def indices05 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,8272#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 8272#u32 5#usize (encodeState value065) 1728#usize
 def indices06 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,9351#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 9351#u32 6#usize (encodeState value066) 1760#usize
 def indices07 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,10385#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 10385#u32 7#usize (encodeState value067) 1792#usize
 def indices08 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,11130#u32,11226#u32,11602#u32,13630#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 11130#u32 8#usize (encodeState value068) 1824#usize
 def indices09 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,11226#u32,11602#u32,13630#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value057,encodeState value058,encodeState value059]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 11226#u32 9#usize (encodeState value069) 1856#usize
 def indices10 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,5613#u32,11602#u32,13630#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value058,encodeState value059]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 11602#u32 10#usize (encodeState value070) 1888#usize
 def indices11 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,5613#u32,5801#u32,13630#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value070,encodeState value059]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 13630#u32 11#usize (encodeState value071) 1920#usize
 def indices12 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,5613#u32,5801#u32,6815#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value070,encodeState value071]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,5613#u32,5801#u32,6815#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value070,encodeState value071]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 1536) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 1920 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 1536 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 893#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 1536 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value048) :=
    JGm_TX2_View.value (s00 s) indices00 values00 1536 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=1536#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠893#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1328#u32,JGm_TX2_View.index (s00 s) indices00 values00 1536 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s00 s).«at» 1568#usize)=ok (encodeState (JGc_TX2_HashBytes.state [91,145,122,197,62,9,154,119,198,228,207,125,51,231,239,131,45,185,107,138,118,76,50,80,150,224,70,82,116,167,73,251])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 48
      5216#usize 1536#usize 1568#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings04.k1c048_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes1 0#usize 0#usize 1#usize 1568#usize 3680#usize
    893#u32 (encodeState value048) (encodeState (JGc_TX2_HashBytes.state [91,145,122,197,62,9,154,119,198,228,207,125,51,231,239,131,45,185,107,138,118,76,50,80,150,224,70,82,116,167,73,251])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read00
  simp only [show 893#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls1.source060 D hash (s00 s) 1#usize 1568#usize 893#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 1568 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 1536 v00
      893#u32 0#usize (encodeState value060) 1568#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 1328#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 1568 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value049) :=
    JGm_TX2_View.value (s01 s) indices01 values01 1568 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=1568#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠1328#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2634#u32,JGm_TX2_View.index (s01 s) indices01 values01 1568 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s01 s).«at» 1600#usize)=ok (encodeState (JGc_TX2_HashBytes.state [90,140,213,237,59,84,110,8,10,122,97,222,95,2,126,163,159,44,250,139,169,14,158,92,31,86,13,238,246,127,219,227])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 49
      5216#usize 1568#usize 1600#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings04.k1c049_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes1 1#usize 1#usize 2#usize 1600#usize 3648#usize
    1328#u32 (encodeState value049) (encodeState (JGc_TX2_HashBytes.state [90,140,213,237,59,84,110,8,10,122,97,222,95,2,126,163,159,44,250,139,169,14,158,92,31,86,13,238,246,127,219,227])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read01
  simp only [show 1328#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls1.source061 D hash (s01 s) 2#usize 1600#usize 1328#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 1600 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 1568 v01
      1328#u32 1#usize (encodeState value061) 1600#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 2634#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 1600 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value050) :=
    JGm_TX2_View.value (s02 s) indices02 values02 1600 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=1600#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠2634#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3461#u32,JGm_TX2_View.index (s02 s) indices02 values02 1600 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s02 s).«at» 1632#usize)=ok (encodeState (JGc_TX2_HashBytes.state [137,141,84,108,125,109,191,204,48,143,71,88,73,187,152,220,129,207,202,11,5,41,190,123,105,166,56,164,25,14,111,64])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 50
      5216#usize 1600#usize 1632#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings04.k1c050_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes1 2#usize 2#usize 3#usize 1632#usize 3616#usize
    2634#u32 (encodeState value050) (encodeState (JGc_TX2_HashBytes.state [137,141,84,108,125,109,191,204,48,143,71,88,73,187,152,220,129,207,202,11,5,41,190,123,105,166,56,164,25,14,111,64])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read02
  simp only [show 2634#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls1.source062 D hash (s02 s) 3#usize 1632#usize 2634#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 1632 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 1600 v02
      2634#u32 2#usize (encodeState value062) 1632#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 3461#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 1632 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value051) :=
    JGm_TX2_View.value (s03 s) indices03 values03 1632 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=1632#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠3461#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3991#u32,JGm_TX2_View.index (s03 s) indices03 values03 1632 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s03 s).«at» 1664#usize)=ok (encodeState (JGc_TX2_HashBytes.state [162,109,78,218,105,211,135,69,9,239,254,91,237,250,215,233,43,236,40,70,170,227,33,222,85,125,177,228,237,172,133,212])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 51
      5216#usize 1632#usize 1664#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings04.k1c051_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes1 3#usize 3#usize 4#usize 1664#usize 3584#usize
    3461#u32 (encodeState value051) (encodeState (JGc_TX2_HashBytes.state [162,109,78,218,105,211,135,69,9,239,254,91,237,250,215,233,43,236,40,70,170,227,33,222,85,125,177,228,237,172,133,212])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read03
  simp only [show 3461#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls1.source063 D hash (s03 s) 4#usize 1664#usize 3461#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 1664 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 1632 v03
      3461#u32 3#usize (encodeState value063) 1664#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 3991#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 1664 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value052) :=
    JGm_TX2_View.value (s04 s) indices04 values04 1664 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=1664#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠3991#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨8272#u32,JGm_TX2_View.index (s04 s) indices04 values04 1664 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s04 s).«at» 1696#usize)=ok (encodeState (JGc_TX2_HashBytes.state [3,177,75,35,72,150,141,238,11,48,28,245,55,173,235,70,132,215,65,116,153,151,30,3,133,217,158,241,55,198,165,163])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 52
      5216#usize 1664#usize 1696#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings04.k1c052_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes1 4#usize 4#usize 5#usize 1696#usize 3552#usize
    3991#u32 (encodeState value052) (encodeState (JGc_TX2_HashBytes.state [3,177,75,35,72,150,141,238,11,48,28,245,55,173,235,70,132,215,65,116,153,151,30,3,133,217,158,241,55,198,165,163])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read04
  simp only [show 3991#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls1.source064 D hash (s04 s) 5#usize 1696#usize 3991#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 1696 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 1664 v04
      3991#u32 4#usize (encodeState value064) 1696#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 8272#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 1696 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value053) :=
    JGm_TX2_View.value (s05 s) indices05 values05 1696 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=1696#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠8272#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨9351#u32,JGm_TX2_View.index (s05 s) indices05 values05 1696 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s05 s).«at» 1728#usize)=ok (encodeState (JGc_TX2_HashBytes.state [7,71,230,53,233,46,37,77,184,75,193,88,35,33,68,235,51,159,237,177,94,144,173,223,233,16,106,87,161,58,177,105])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 53
      5216#usize 1696#usize 1728#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings04.k1c053_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes1 5#usize 5#usize 6#usize 1728#usize 3520#usize
    8272#u32 (encodeState value053) (encodeState (JGc_TX2_HashBytes.state [7,71,230,53,233,46,37,77,184,75,193,88,35,33,68,235,51,159,237,177,94,144,173,223,233,16,106,87,161,58,177,105])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read05
  simp only [show 8272#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls1.source065 D hash (s05 s) 6#usize 1728#usize 8272#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 1728 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 1696 v05
      8272#u32 5#usize (encodeState value065) 1728#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 9351#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 1728 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value054) :=
    JGm_TX2_View.value (s06 s) indices06 values06 1728 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=1728#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠9351#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨10385#u32,JGm_TX2_View.index (s06 s) indices06 values06 1728 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s06 s).«at» 1760#usize)=ok (encodeState (JGc_TX2_HashBytes.state [100,208,206,178,211,104,93,209,84,229,201,209,70,62,177,3,162,49,77,164,166,198,88,39,148,11,159,214,254,213,150,193])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 54
      5216#usize 1728#usize 1760#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings04.k1c054_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes1 6#usize 6#usize 7#usize 1760#usize 3488#usize
    9351#u32 (encodeState value054) (encodeState (JGc_TX2_HashBytes.state [100,208,206,178,211,104,93,209,84,229,201,209,70,62,177,3,162,49,77,164,166,198,88,39,148,11,159,214,254,213,150,193])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read06
  simp only [show 9351#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls1.source066 D hash (s06 s) 7#usize 1760#usize 9351#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 1760 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 1728 v06
      9351#u32 6#usize (encodeState value066) 1760#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 10385#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 1760 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value055) :=
    JGm_TX2_View.value (s07 s) indices07 values07 1760 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=1760#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠10385#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨11130#u32,JGm_TX2_View.index (s07 s) indices07 values07 1760 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s07 s).«at» 1792#usize)=ok (encodeState (JGc_TX2_HashBytes.state [204,138,128,220,43,110,243,42,112,197,80,64,180,242,245,200,51,70,22,140,85,234,163,241,149,58,99,176,37,185,89,70])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 55
      5216#usize 1760#usize 1792#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings04.k1c055_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes1 7#usize 7#usize 8#usize 1792#usize 3456#usize
    10385#u32 (encodeState value055) (encodeState (JGc_TX2_HashBytes.state [204,138,128,220,43,110,243,42,112,197,80,64,180,242,245,200,51,70,22,140,85,234,163,241,149,58,99,176,37,185,89,70])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read07
  simp only [show 10385#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls1.source067 D hash (s07 s) 8#usize 1792#usize 10385#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 1792 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 1760 v07
      10385#u32 7#usize (encodeState value067) 1792#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 11130#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 1792 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value056) :=
    JGm_TX2_View.value (s08 s) indices08 values08 1792 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=1792#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠11130#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨11226#u32,JGm_TX2_View.index (s08 s) indices08 values08 1792 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s08 s).«at» 1824#usize)=ok (encodeState (JGc_TX2_HashBytes.state [100,75,61,102,95,187,38,76,72,111,199,89,100,106,122,95,239,187,212,134,17,10,153,71,129,234,125,216,197,105,64,123])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 56
      5216#usize 1792#usize 1824#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings04.k1c056_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes1 8#usize 8#usize 9#usize 1824#usize 3424#usize
    11130#u32 (encodeState value056) (encodeState (JGc_TX2_HashBytes.state [100,75,61,102,95,187,38,76,72,111,199,89,100,106,122,95,239,187,212,134,17,10,153,71,129,234,125,216,197,105,64,123])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read08
  simp only [show 11130#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls1.source068 D hash (s08 s) 9#usize 1824#usize 11130#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 1824 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 1792 v08
      11130#u32 8#usize (encodeState value068) 1824#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 11226#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 1824 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value057) :=
    JGm_TX2_View.value (s09 s) indices09 values09 1824 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=1824#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠11226#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨11602#u32,JGm_TX2_View.index (s09 s) indices09 values09 1824 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s09 s).«at» 1856#usize)=ok (encodeState (JGc_TX2_HashBytes.state [192,203,122,95,19,169,3,216,182,71,243,115,97,181,77,86,174,198,18,233,61,203,165,112,193,236,213,83,40,40,150,3])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 57
      5216#usize 1824#usize 1856#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings04.k1c057_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes1 9#usize 9#usize 10#usize 1856#usize 3392#usize
    11226#u32 (encodeState value057) (encodeState (JGc_TX2_HashBytes.state [192,203,122,95,19,169,3,216,182,71,243,115,97,181,77,86,174,198,18,233,61,203,165,112,193,236,213,83,40,40,150,3])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read09
  simp only [show 11226#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls1.source069 D hash (s09 s) 10#usize 1856#usize 11226#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 1856 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 1824 v09
      11226#u32 9#usize (encodeState value069) 1856#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 11602#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 1856 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value058) :=
    JGm_TX2_View.value (s10 s) indices10 values10 1856 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=1856#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠11602#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨13630#u32,JGm_TX2_View.index (s10 s) indices10 values10 1856 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s10 s).«at» 1888#usize)=ok (encodeState (JGc_TX2_HashBytes.state [49,2,133,245,85,142,142,39,72,171,94,251,203,163,145,100,127,163,255,58,90,160,38,46,170,45,166,44,55,55,154,112])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 58
      5216#usize 1856#usize 1888#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings04.k1c058_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes1 10#usize 10#usize 11#usize 1888#usize 3360#usize
    11602#u32 (encodeState value058) (encodeState (JGc_TX2_HashBytes.state [49,2,133,245,85,142,142,39,72,171,94,251,203,163,145,100,127,163,255,58,90,160,38,46,170,45,166,44,55,55,154,112])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read10
  simp only [show 11602#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes1 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls1.source070 D hash (s10 s) 11#usize 1888#usize 11602#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 1888 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 1856 v10
      11602#u32 10#usize (encodeState value070) 1888#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 13630#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 1888 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value059) :=
    JGm_TX2_View.value (s11 s) indices11 values11 1888 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=1888#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠13630#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s11 s).«at» 1920#usize)=ok (encodeState (JGc_TX2_HashBytes.state [37,136,167,16,131,171,200,73,63,75,48,101,141,75,3,143,138,38,137,9,54,123,113,130,73,175,89,214,32,212,174,7])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 59
      5216#usize 1888#usize 1920#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings04.k1c059_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes1 11#usize 11#usize 12#usize 1920#usize 3328#usize
    13630#u32 (encodeState value059) (encodeState (JGc_TX2_HashBytes.state [37,136,167,16,131,171,200,73,63,75,48,101,141,75,3,143,138,38,137,9,54,123,113,130,73,175,89,214,32,212,174,7])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read11
  simp only [show 13630#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes1 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls1.source071 D hash (s11 s) 12#usize 1920#usize 13630#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 1920 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 1888 v11
      13630#u32 11#usize (encodeState value071) 1920#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 1920
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level1_04
end
