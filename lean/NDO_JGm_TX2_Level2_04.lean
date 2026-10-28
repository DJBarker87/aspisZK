import NDO_JGm_TX2_ParentCalls2
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level2_04
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGc_TX2_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes2
def indices00 : List U32 := [223#u32,332#u32,658#u32,865#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
def values00 : List (Array U8 32#usize) := [encodeState value048,encodeState value049,encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 223#u32 0#usize (encodeState value060) 1568#usize
 def indices01 : List U32 := [111#u32,332#u32,658#u32,865#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value060,encodeState value049,encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 332#u32 1#usize (encodeState value061) 1600#usize
 def indices02 : List U32 := [111#u32,166#u32,658#u32,865#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value050,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 658#u32 2#usize (encodeState value062) 1632#usize
 def indices03 : List U32 := [111#u32,166#u32,329#u32,865#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value051,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 865#u32 3#usize (encodeState value063) 1664#usize
 def indices04 : List U32 := [111#u32,166#u32,329#u32,432#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value052,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 997#u32 4#usize (encodeState value064) 1696#usize
 def indices05 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value053,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 2068#u32 5#usize (encodeState value065) 1728#usize
 def indices06 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value054,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 2337#u32 6#usize (encodeState value066) 1760#usize
 def indices07 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value055,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 2596#u32 7#usize (encodeState value067) 1792#usize
 def indices08 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value056,encodeState value057,encodeState value058,encodeState value059]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 2782#u32 8#usize (encodeState value068) 1824#usize
 def indices09 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,2806#u32,2900#u32,3407#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value057,encodeState value058,encodeState value059]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 2806#u32 9#usize (encodeState value069) 1856#usize
 def indices10 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,1403#u32,2900#u32,3407#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value058,encodeState value059]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 2900#u32 10#usize (encodeState value070) 1888#usize
 def indices11 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,1403#u32,1450#u32,3407#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value070,encodeState value059]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 3407#u32 11#usize (encodeState value071) 1920#usize
 def indices12 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,1403#u32,1450#u32,1703#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value070,encodeState value071]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,1403#u32,1450#u32,1703#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value060,encodeState value061,encodeState value062,encodeState value063,encodeState value064,encodeState value065,encodeState value066,encodeState value067,encodeState value068,encodeState value069,encodeState value070,encodeState value071]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 1536) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 1920 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 1536 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 223#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 1536 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value048) :=
    JGm_TX2_View.value (s00 s) indices00 values00 1536 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=1536#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠223#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨332#u32,JGm_TX2_View.index (s00 s) indices00 values00 1536 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s00 s).«at» 1568#usize)=ok (encodeState (JGc_TX2_HashBytes.state [247,100,236,140,76,132,72,103,230,182,217,150,219,250,252,178,17,5,14,17,110,183,246,163,82,227,58,184,169,136,239,158])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 48
      4512#usize 1536#usize 1568#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings04.k2c048_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes2 0#usize 0#usize 1#usize 1568#usize 2976#usize
    223#u32 (encodeState value048) (encodeState (JGc_TX2_HashBytes.state [247,100,236,140,76,132,72,103,230,182,217,150,219,250,252,178,17,5,14,17,110,183,246,163,82,227,58,184,169,136,239,158])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read00
  simp only [show 223#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls2.source060 D hash (s00 s) 1#usize 1568#usize 223#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 1568 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 1536 v00
      223#u32 0#usize (encodeState value060) 1568#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 332#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 1568 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value049) :=
    JGm_TX2_View.value (s01 s) indices01 values01 1568 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=1568#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠332#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨658#u32,JGm_TX2_View.index (s01 s) indices01 values01 1568 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s01 s).«at» 1600#usize)=ok (encodeState (JGc_TX2_HashBytes.state [175,214,251,74,56,98,215,165,147,235,8,16,138,10,129,140,104,24,70,95,255,124,239,8,248,145,212,161,195,57,205,112])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 49
      4512#usize 1568#usize 1600#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings04.k2c049_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes2 1#usize 1#usize 2#usize 1600#usize 2944#usize
    332#u32 (encodeState value049) (encodeState (JGc_TX2_HashBytes.state [175,214,251,74,56,98,215,165,147,235,8,16,138,10,129,140,104,24,70,95,255,124,239,8,248,145,212,161,195,57,205,112])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read01
  simp only [show 332#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls2.source061 D hash (s01 s) 2#usize 1600#usize 332#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 1600 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 1568 v01
      332#u32 1#usize (encodeState value061) 1600#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 658#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 1600 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value050) :=
    JGm_TX2_View.value (s02 s) indices02 values02 1600 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=1600#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠658#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨865#u32,JGm_TX2_View.index (s02 s) indices02 values02 1600 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s02 s).«at» 1632#usize)=ok (encodeState (JGc_TX2_HashBytes.state [220,217,136,94,221,196,15,137,224,208,19,77,144,180,208,70,235,172,5,103,9,159,38,30,58,148,186,113,174,237,185,9])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 50
      4512#usize 1600#usize 1632#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings04.k2c050_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes2 2#usize 2#usize 3#usize 1632#usize 2912#usize
    658#u32 (encodeState value050) (encodeState (JGc_TX2_HashBytes.state [220,217,136,94,221,196,15,137,224,208,19,77,144,180,208,70,235,172,5,103,9,159,38,30,58,148,186,113,174,237,185,9])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read02
  simp only [show 658#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls2.source062 D hash (s02 s) 3#usize 1632#usize 658#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 1632 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 1600 v02
      658#u32 2#usize (encodeState value062) 1632#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 865#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 1632 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value051) :=
    JGm_TX2_View.value (s03 s) indices03 values03 1632 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=1632#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠865#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨997#u32,JGm_TX2_View.index (s03 s) indices03 values03 1632 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s03 s).«at» 1664#usize)=ok (encodeState (JGc_TX2_HashBytes.state [240,86,123,40,144,253,125,166,16,245,72,190,206,15,158,196,221,57,211,112,69,169,129,144,132,13,152,226,128,228,247,41])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 51
      4512#usize 1632#usize 1664#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings04.k2c051_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes2 3#usize 3#usize 4#usize 1664#usize 2880#usize
    865#u32 (encodeState value051) (encodeState (JGc_TX2_HashBytes.state [240,86,123,40,144,253,125,166,16,245,72,190,206,15,158,196,221,57,211,112,69,169,129,144,132,13,152,226,128,228,247,41])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read03
  simp only [show 865#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes2 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls2.source063 D hash (s03 s) 4#usize 1664#usize 865#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 1664 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 1632 v03
      865#u32 3#usize (encodeState value063) 1664#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 997#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 1664 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value052) :=
    JGm_TX2_View.value (s04 s) indices04 values04 1664 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=1664#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠997#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2068#u32,JGm_TX2_View.index (s04 s) indices04 values04 1664 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s04 s).«at» 1696#usize)=ok (encodeState (JGc_TX2_HashBytes.state [9,238,254,255,39,254,243,46,95,21,236,63,187,8,183,169,44,166,37,80,101,37,29,79,232,151,122,161,132,199,220,125])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 52
      4512#usize 1664#usize 1696#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings04.k2c052_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes2 4#usize 4#usize 5#usize 1696#usize 2848#usize
    997#u32 (encodeState value052) (encodeState (JGc_TX2_HashBytes.state [9,238,254,255,39,254,243,46,95,21,236,63,187,8,183,169,44,166,37,80,101,37,29,79,232,151,122,161,132,199,220,125])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read04
  simp only [show 997#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes2 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls2.source064 D hash (s04 s) 5#usize 1696#usize 997#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 1696 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 1664 v04
      997#u32 4#usize (encodeState value064) 1696#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 2068#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 1696 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value053) :=
    JGm_TX2_View.value (s05 s) indices05 values05 1696 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=1696#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠2068#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2337#u32,JGm_TX2_View.index (s05 s) indices05 values05 1696 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s05 s).«at» 1728#usize)=ok (encodeState (JGc_TX2_HashBytes.state [100,212,44,109,255,78,23,21,146,213,56,218,252,246,125,196,178,169,158,114,87,64,92,68,191,82,154,132,247,33,109,192])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 53
      4512#usize 1696#usize 1728#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings04.k2c053_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes2 5#usize 5#usize 6#usize 1728#usize 2816#usize
    2068#u32 (encodeState value053) (encodeState (JGc_TX2_HashBytes.state [100,212,44,109,255,78,23,21,146,213,56,218,252,246,125,196,178,169,158,114,87,64,92,68,191,82,154,132,247,33,109,192])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read05
  simp only [show 2068#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes2 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls2.source065 D hash (s05 s) 6#usize 1728#usize 2068#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 1728 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 1696 v05
      2068#u32 5#usize (encodeState value065) 1728#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 2337#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 1728 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value054) :=
    JGm_TX2_View.value (s06 s) indices06 values06 1728 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=1728#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠2337#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2596#u32,JGm_TX2_View.index (s06 s) indices06 values06 1728 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s06 s).«at» 1760#usize)=ok (encodeState (JGc_TX2_HashBytes.state [245,72,84,194,109,47,181,252,233,38,6,190,122,213,219,166,146,217,99,248,71,208,31,100,80,120,165,181,91,203,136,110])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 54
      4512#usize 1728#usize 1760#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings04.k2c054_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes2 6#usize 6#usize 7#usize 1760#usize 2784#usize
    2337#u32 (encodeState value054) (encodeState (JGc_TX2_HashBytes.state [245,72,84,194,109,47,181,252,233,38,6,190,122,213,219,166,146,217,99,248,71,208,31,100,80,120,165,181,91,203,136,110])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read06
  simp only [show 2337#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes2 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls2.source066 D hash (s06 s) 7#usize 1760#usize 2337#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 1760 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 1728 v06
      2337#u32 6#usize (encodeState value066) 1760#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 2596#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 1760 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value055) :=
    JGm_TX2_View.value (s07 s) indices07 values07 1760 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=1760#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠2596#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2782#u32,JGm_TX2_View.index (s07 s) indices07 values07 1760 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s07 s).«at» 1792#usize)=ok (encodeState (JGc_TX2_HashBytes.state [106,188,178,230,119,169,216,143,108,241,225,128,42,214,225,250,113,247,35,216,252,247,44,106,56,109,25,126,244,160,227,251])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 55
      4512#usize 1760#usize 1792#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings04.k2c055_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes2 7#usize 7#usize 8#usize 1792#usize 2752#usize
    2596#u32 (encodeState value055) (encodeState (JGc_TX2_HashBytes.state [106,188,178,230,119,169,216,143,108,241,225,128,42,214,225,250,113,247,35,216,252,247,44,106,56,109,25,126,244,160,227,251])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read07
  simp only [show 2596#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes2 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls2.source067 D hash (s07 s) 8#usize 1792#usize 2596#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 1792 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 1760 v07
      2596#u32 7#usize (encodeState value067) 1792#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 2782#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 1792 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value056) :=
    JGm_TX2_View.value (s08 s) indices08 values08 1792 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=1792#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠2782#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2806#u32,JGm_TX2_View.index (s08 s) indices08 values08 1792 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s08 s).«at» 1824#usize)=ok (encodeState (JGc_TX2_HashBytes.state [155,130,8,91,15,187,131,135,196,217,122,123,47,107,17,16,212,157,238,253,47,129,67,155,161,159,151,86,58,173,37,177])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 56
      4512#usize 1792#usize 1824#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings04.k2c056_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes2 8#usize 8#usize 9#usize 1824#usize 2720#usize
    2782#u32 (encodeState value056) (encodeState (JGc_TX2_HashBytes.state [155,130,8,91,15,187,131,135,196,217,122,123,47,107,17,16,212,157,238,253,47,129,67,155,161,159,151,86,58,173,37,177])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read08
  simp only [show 2782#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes2 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls2.source068 D hash (s08 s) 9#usize 1824#usize 2782#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 1824 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 1792 v08
      2782#u32 8#usize (encodeState value068) 1824#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 2806#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 1824 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value057) :=
    JGm_TX2_View.value (s09 s) indices09 values09 1824 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=1824#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠2806#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2900#u32,JGm_TX2_View.index (s09 s) indices09 values09 1824 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s09 s).«at» 1856#usize)=ok (encodeState (JGc_TX2_HashBytes.state [197,243,223,90,252,37,18,71,199,122,73,100,251,196,134,181,134,250,69,242,47,132,11,63,218,201,169,244,244,50,29,163])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 57
      4512#usize 1824#usize 1856#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings04.k2c057_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes2 9#usize 9#usize 10#usize 1856#usize 2688#usize
    2806#u32 (encodeState value057) (encodeState (JGc_TX2_HashBytes.state [197,243,223,90,252,37,18,71,199,122,73,100,251,196,134,181,134,250,69,242,47,132,11,63,218,201,169,244,244,50,29,163])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read09
  simp only [show 2806#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes2 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls2.source069 D hash (s09 s) 10#usize 1856#usize 2806#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 1856 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 1824 v09
      2806#u32 9#usize (encodeState value069) 1856#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 2900#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 1856 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value058) :=
    JGm_TX2_View.value (s10 s) indices10 values10 1856 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=1856#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠2900#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3407#u32,JGm_TX2_View.index (s10 s) indices10 values10 1856 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s10 s).«at» 1888#usize)=ok (encodeState (JGc_TX2_HashBytes.state [41,80,148,57,53,114,10,3,122,75,219,82,120,38,161,206,250,203,250,125,171,10,160,248,198,226,154,77,68,219,2,125])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 58
      4512#usize 1856#usize 1888#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings04.k2c058_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes2 10#usize 10#usize 11#usize 1888#usize 2656#usize
    2900#u32 (encodeState value058) (encodeState (JGc_TX2_HashBytes.state [41,80,148,57,53,114,10,3,122,75,219,82,120,38,161,206,250,203,250,125,171,10,160,248,198,226,154,77,68,219,2,125])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read10
  simp only [show 2900#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes2 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls2.source070 D hash (s10 s) 11#usize 1888#usize 2900#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 1888 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 1856 v10
      2900#u32 10#usize (encodeState value070) 1888#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 3407#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 1888 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value059) :=
    JGm_TX2_View.value (s11 s) indices11 values11 1888 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=1888#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠3407#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s11 s).«at» 1920#usize)=ok (encodeState (JGc_TX2_HashBytes.state [179,249,234,136,136,173,217,82,176,51,76,226,205,86,174,215,92,34,110,234,232,9,110,135,142,4,169,245,40,230,2,165])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 59
      4512#usize 1888#usize 1920#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings04.k2c059_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes2 11#usize 11#usize 12#usize 1920#usize 2624#usize
    3407#u32 (encodeState value059) (encodeState (JGc_TX2_HashBytes.state [179,249,234,136,136,173,217,82,176,51,76,226,205,86,174,215,92,34,110,234,232,9,110,135,142,4,169,245,40,230,2,165])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read11
  simp only [show 3407#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes2 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls2.source071 D hash (s11 s) 12#usize 1920#usize 3407#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 1920 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 1888 v11
      3407#u32 11#usize (encodeState value071) 1920#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 1920
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level2_04
end
