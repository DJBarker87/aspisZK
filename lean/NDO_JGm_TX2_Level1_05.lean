import NDO_JGm_TX2_ParentCalls1
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level1_05
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGh_TX2_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes1
def indices00 : List U32 := [446#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,5613#u32,5801#u32,6815#u32]
def values00 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value070,encodeState value071]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 446#u32 0#usize (encodeState value072) 1952#usize
 def indices01 : List U32 := [223#u32,664#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,5613#u32,5801#u32,6815#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value072,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value070,encodeState value071]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 664#u32 1#usize (encodeState value073) 1984#usize
 def indices02 : List U32 := [223#u32,332#u32,1317#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,5613#u32,5801#u32,6815#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value072,encodeState value073,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value070,encodeState value071]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 1317#u32 2#usize (encodeState value074) 2016#usize
 def indices03 : List U32 := [223#u32,332#u32,658#u32,1730#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,5613#u32,5801#u32,6815#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value072,encodeState value073,encodeState value074,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value070,encodeState value071]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 1730#u32 3#usize (encodeState value075) 2048#usize
 def indices04 : List U32 := [223#u32,332#u32,658#u32,865#u32,1995#u32,4136#u32,4675#u32,5192#u32,5565#u32,5613#u32,5801#u32,6815#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value070,encodeState value071]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 1995#u32 4#usize (encodeState value076) 2080#usize
 def indices05 : List U32 := [223#u32,332#u32,658#u32,865#u32,997#u32,4136#u32,4675#u32,5192#u32,5565#u32,5613#u32,5801#u32,6815#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value070,encodeState value071]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 4136#u32 5#usize (encodeState value077) 2112#usize
 def indices06 : List U32 := [223#u32,332#u32,658#u32,865#u32,997#u32,2068#u32,4675#u32,5192#u32,5565#u32,5613#u32,5801#u32,6815#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value070,encodeState value071]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 4675#u32 6#usize (encodeState value078) 2144#usize
 def indices07 : List U32 := [223#u32,332#u32,658#u32,865#u32,997#u32,2068#u32,2337#u32,5192#u32,5565#u32,5613#u32,5801#u32,6815#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value067,encodeState value068,encodeState value069,encodeState value070,encodeState value071]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 5192#u32 7#usize (encodeState value079) 2176#usize
 def indices08 : List U32 := [223#u32,332#u32,658#u32,865#u32,997#u32,2068#u32,2337#u32,2596#u32,5565#u32,5613#u32,5801#u32,6815#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value068,encodeState value069,encodeState value070,encodeState value071]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 5565#u32 8#usize (encodeState value080) 2208#usize
 def indices09 : List U32 := [223#u32,332#u32,658#u32,865#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,5613#u32,5801#u32,6815#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value069,encodeState value070,encodeState value071]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 5613#u32 9#usize (encodeState value081) 2240#usize
 def indices10 : List U32 := [223#u32,332#u32,658#u32,865#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,5801#u32,6815#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value070,encodeState value071]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 5801#u32 10#usize (encodeState value082) 2272#usize
 def indices11 : List U32 := [223#u32,332#u32,658#u32,865#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,6815#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value071]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 6815#u32 11#usize (encodeState value083) 2304#usize
 def indices12 : List U32 := [223#u32,332#u32,658#u32,865#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [223#u32,332#u32,658#u32,865#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 1920) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 2304 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 1920 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 446#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 1920 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value060) :=
    JGm_TX2_View.value (s00 s) indices00 values00 1920 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=1920#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠446#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨664#u32,JGm_TX2_View.index (s00 s) indices00 values00 1920 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s00 s).«at» 1952#usize)=ok (encodeState (JGc_TX2_HashBytes.state [146,241,209,76,3,149,10,93,27,213,253,187,235,215,249,224,226,149,246,181,179,76,247,230,164,235,95,209,146,119,118,116])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 60
      5216#usize 1920#usize 1952#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings05.k1c060_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes1 0#usize 0#usize 1#usize 1952#usize 3296#usize
    446#u32 (encodeState value060) (encodeState (JGc_TX2_HashBytes.state [146,241,209,76,3,149,10,93,27,213,253,187,235,215,249,224,226,149,246,181,179,76,247,230,164,235,95,209,146,119,118,116])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read00
  simp only [show 446#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls1.source072 D hash (s00 s) 1#usize 1952#usize 446#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 1952 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 1920 v00
      446#u32 0#usize (encodeState value072) 1952#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 664#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 1952 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value061) :=
    JGm_TX2_View.value (s01 s) indices01 values01 1952 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=1952#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠664#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1317#u32,JGm_TX2_View.index (s01 s) indices01 values01 1952 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s01 s).«at» 1984#usize)=ok (encodeState (JGc_TX2_HashBytes.state [196,97,185,89,51,243,48,45,26,150,114,27,15,171,6,81,176,135,118,176,30,215,223,61,49,51,111,107,216,68,215,163])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 61
      5216#usize 1952#usize 1984#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings05.k1c061_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes1 1#usize 1#usize 2#usize 1984#usize 3264#usize
    664#u32 (encodeState value061) (encodeState (JGc_TX2_HashBytes.state [196,97,185,89,51,243,48,45,26,150,114,27,15,171,6,81,176,135,118,176,30,215,223,61,49,51,111,107,216,68,215,163])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read01
  simp only [show 664#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls1.source073 D hash (s01 s) 2#usize 1984#usize 664#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 1984 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 1952 v01
      664#u32 1#usize (encodeState value073) 1984#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 1317#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 1984 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value062) :=
    JGm_TX2_View.value (s02 s) indices02 values02 1984 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=1984#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠1317#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1730#u32,JGm_TX2_View.index (s02 s) indices02 values02 1984 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s02 s).«at» 2016#usize)=ok (encodeState (JGc_TX2_HashBytes.state [95,226,211,110,59,1,240,84,89,16,140,12,55,255,250,31,115,169,60,16,164,241,70,183,235,108,196,68,104,88,159,123])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 62
      5216#usize 1984#usize 2016#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings05.k1c062_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes1 2#usize 2#usize 3#usize 2016#usize 3232#usize
    1317#u32 (encodeState value062) (encodeState (JGc_TX2_HashBytes.state [95,226,211,110,59,1,240,84,89,16,140,12,55,255,250,31,115,169,60,16,164,241,70,183,235,108,196,68,104,88,159,123])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read02
  simp only [show 1317#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls1.source074 D hash (s02 s) 3#usize 2016#usize 1317#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 2016 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 1984 v02
      1317#u32 2#usize (encodeState value074) 2016#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 1730#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 2016 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value063) :=
    JGm_TX2_View.value (s03 s) indices03 values03 2016 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=2016#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠1730#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1995#u32,JGm_TX2_View.index (s03 s) indices03 values03 2016 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s03 s).«at» 2048#usize)=ok (encodeState (JGc_TX2_HashBytes.state [39,102,38,180,186,61,172,204,136,19,30,66,35,48,23,185,218,112,25,123,68,164,35,16,11,242,162,81,250,162,61,20])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 63
      5216#usize 2016#usize 2048#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings05.k1c063_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes1 3#usize 3#usize 4#usize 2048#usize 3200#usize
    1730#u32 (encodeState value063) (encodeState (JGc_TX2_HashBytes.state [39,102,38,180,186,61,172,204,136,19,30,66,35,48,23,185,218,112,25,123,68,164,35,16,11,242,162,81,250,162,61,20])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read03
  simp only [show 1730#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls1.source075 D hash (s03 s) 4#usize 2048#usize 1730#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 2048 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 2016 v03
      1730#u32 3#usize (encodeState value075) 2048#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 1995#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 2048 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value064) :=
    JGm_TX2_View.value (s04 s) indices04 values04 2048 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=2048#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠1995#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨4136#u32,JGm_TX2_View.index (s04 s) indices04 values04 2048 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s04 s).«at» 2080#usize)=ok (encodeState (JGc_TX2_HashBytes.state [78,86,254,186,143,139,176,192,161,97,48,153,109,78,105,243,56,37,123,22,134,184,234,220,103,58,193,102,154,216,217,249])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 64
      5216#usize 2048#usize 2080#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings05.k1c064_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes1 4#usize 4#usize 5#usize 2080#usize 3168#usize
    1995#u32 (encodeState value064) (encodeState (JGc_TX2_HashBytes.state [78,86,254,186,143,139,176,192,161,97,48,153,109,78,105,243,56,37,123,22,134,184,234,220,103,58,193,102,154,216,217,249])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read04
  simp only [show 1995#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls1.source076 D hash (s04 s) 5#usize 2080#usize 1995#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 2080 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 2048 v04
      1995#u32 4#usize (encodeState value076) 2080#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 4136#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 2080 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value065) :=
    JGm_TX2_View.value (s05 s) indices05 values05 2080 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=2080#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠4136#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨4675#u32,JGm_TX2_View.index (s05 s) indices05 values05 2080 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s05 s).«at» 2112#usize)=ok (encodeState (JGc_TX2_HashBytes.state [6,176,225,182,142,20,8,178,54,9,77,35,23,17,211,21,117,198,146,72,194,14,187,107,107,174,152,17,225,13,237,28])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 65
      5216#usize 2080#usize 2112#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings05.k1c065_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes1 5#usize 5#usize 6#usize 2112#usize 3136#usize
    4136#u32 (encodeState value065) (encodeState (JGc_TX2_HashBytes.state [6,176,225,182,142,20,8,178,54,9,77,35,23,17,211,21,117,198,146,72,194,14,187,107,107,174,152,17,225,13,237,28])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read05
  simp only [show 4136#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls1.source077 D hash (s05 s) 6#usize 2112#usize 4136#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 2112 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 2080 v05
      4136#u32 5#usize (encodeState value077) 2112#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 4675#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 2112 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value066) :=
    JGm_TX2_View.value (s06 s) indices06 values06 2112 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=2112#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠4675#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨5192#u32,JGm_TX2_View.index (s06 s) indices06 values06 2112 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s06 s).«at» 2144#usize)=ok (encodeState (JGc_TX2_HashBytes.state [35,192,208,97,49,197,76,230,222,37,155,218,108,241,151,228,251,160,197,104,117,82,209,205,160,243,80,118,172,74,173,90])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 66
      5216#usize 2112#usize 2144#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings05.k1c066_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes1 6#usize 6#usize 7#usize 2144#usize 3104#usize
    4675#u32 (encodeState value066) (encodeState (JGc_TX2_HashBytes.state [35,192,208,97,49,197,76,230,222,37,155,218,108,241,151,228,251,160,197,104,117,82,209,205,160,243,80,118,172,74,173,90])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read06
  simp only [show 4675#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls1.source078 D hash (s06 s) 7#usize 2144#usize 4675#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 2144 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 2112 v06
      4675#u32 6#usize (encodeState value078) 2144#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 5192#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 2144 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value067) :=
    JGm_TX2_View.value (s07 s) indices07 values07 2144 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=2144#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠5192#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨5565#u32,JGm_TX2_View.index (s07 s) indices07 values07 2144 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s07 s).«at» 2176#usize)=ok (encodeState (JGc_TX2_HashBytes.state [2,200,91,35,17,31,94,75,75,122,111,112,173,132,168,88,8,67,99,174,60,147,115,83,65,202,86,17,3,156,44,87])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 67
      5216#usize 2144#usize 2176#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings05.k1c067_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes1 7#usize 7#usize 8#usize 2176#usize 3072#usize
    5192#u32 (encodeState value067) (encodeState (JGc_TX2_HashBytes.state [2,200,91,35,17,31,94,75,75,122,111,112,173,132,168,88,8,67,99,174,60,147,115,83,65,202,86,17,3,156,44,87])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read07
  simp only [show 5192#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls1.source079 D hash (s07 s) 8#usize 2176#usize 5192#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 2176 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 2144 v07
      5192#u32 7#usize (encodeState value079) 2176#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 5565#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 2176 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value068) :=
    JGm_TX2_View.value (s08 s) indices08 values08 2176 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=2176#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠5565#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨5613#u32,JGm_TX2_View.index (s08 s) indices08 values08 2176 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s08 s).«at» 2208#usize)=ok (encodeState (JGc_TX2_HashBytes.state [47,38,233,59,180,35,70,129,102,50,66,0,6,148,186,196,185,192,124,243,85,64,33,178,120,201,86,191,194,96,242,179])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 68
      5216#usize 2176#usize 2208#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings05.k1c068_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes1 8#usize 8#usize 9#usize 2208#usize 3040#usize
    5565#u32 (encodeState value068) (encodeState (JGc_TX2_HashBytes.state [47,38,233,59,180,35,70,129,102,50,66,0,6,148,186,196,185,192,124,243,85,64,33,178,120,201,86,191,194,96,242,179])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read08
  simp only [show 5565#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls1.source080 D hash (s08 s) 9#usize 2208#usize 5565#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 2208 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 2176 v08
      5565#u32 8#usize (encodeState value080) 2208#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 5613#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 2208 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value069) :=
    JGm_TX2_View.value (s09 s) indices09 values09 2208 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=2208#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠5613#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨5801#u32,JGm_TX2_View.index (s09 s) indices09 values09 2208 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s09 s).«at» 2240#usize)=ok (encodeState (JGc_TX2_HashBytes.state [125,8,110,233,101,85,136,4,49,158,25,196,30,207,11,227,60,89,21,199,168,171,114,40,120,158,191,202,149,105,205,232])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 69
      5216#usize 2208#usize 2240#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings05.k1c069_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes1 9#usize 9#usize 10#usize 2240#usize 3008#usize
    5613#u32 (encodeState value069) (encodeState (JGc_TX2_HashBytes.state [125,8,110,233,101,85,136,4,49,158,25,196,30,207,11,227,60,89,21,199,168,171,114,40,120,158,191,202,149,105,205,232])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read09
  simp only [show 5613#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls1.source081 D hash (s09 s) 10#usize 2240#usize 5613#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 2240 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 2208 v09
      5613#u32 9#usize (encodeState value081) 2240#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 5801#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 2240 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value070) :=
    JGm_TX2_View.value (s10 s) indices10 values10 2240 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=2240#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠5801#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨6815#u32,JGm_TX2_View.index (s10 s) indices10 values10 2240 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s10 s).«at» 2272#usize)=ok (encodeState (JGc_TX2_HashBytes.state [159,146,135,36,118,126,128,186,60,135,70,34,70,59,162,240,237,150,157,75,246,206,33,126,246,48,220,254,15,29,8,210])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 70
      5216#usize 2240#usize 2272#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings05.k1c070_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes1 10#usize 10#usize 11#usize 2272#usize 2976#usize
    5801#u32 (encodeState value070) (encodeState (JGc_TX2_HashBytes.state [159,146,135,36,118,126,128,186,60,135,70,34,70,59,162,240,237,150,157,75,246,206,33,126,246,48,220,254,15,29,8,210])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read10
  simp only [show 5801#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes1 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls1.source082 D hash (s10 s) 11#usize 2272#usize 5801#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 2272 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 2240 v10
      5801#u32 10#usize (encodeState value082) 2272#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 6815#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 2272 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value071) :=
    JGm_TX2_View.value (s11 s) indices11 values11 2272 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=2272#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠6815#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s11 s).«at» 2304#usize)=ok (encodeState (JGc_TX2_HashBytes.state [40,162,122,51,11,161,127,39,189,8,128,48,186,50,21,86,72,85,188,173,133,84,193,242,173,138,242,218,19,169,118,246])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 71
      5216#usize 2272#usize 2304#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings05.k1c071_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes1 11#usize 11#usize 12#usize 2304#usize 2944#usize
    6815#u32 (encodeState value071) (encodeState (JGc_TX2_HashBytes.state [40,162,122,51,11,161,127,39,189,8,128,48,186,50,21,86,72,85,188,173,133,84,193,242,173,138,242,218,19,169,118,246])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read11
  simp only [show 6815#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes1 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls1.source083 D hash (s11 s) 12#usize 2304#usize 6815#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 2304 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 2272 v11
      6815#u32 11#usize (encodeState value083) 2304#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 2304
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level1_05
end
