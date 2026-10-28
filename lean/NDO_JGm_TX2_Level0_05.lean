import NDO_JGm_TX2_ParentCalls0
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level0_05
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGf_TX2_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes0
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
      s JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
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
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s00 s).«at» 1952#usize)=ok (encodeState (JGc_TX2_HashBytes.state [231,229,212,57,61,52,13,131,98,196,105,18,170,125,180,159,155,88,136,210,120,50,162,252,183,109,92,145,239,186,61,138])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 60
      5216#usize 1920#usize 1952#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings05.k0c060_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes0 0#usize 0#usize 1#usize 1952#usize 3296#usize
    446#u32 (encodeState value060) (encodeState (JGc_TX2_HashBytes.state [231,229,212,57,61,52,13,131,98,196,105,18,170,125,180,159,155,88,136,210,120,50,162,252,183,109,92,145,239,186,61,138])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read00
  simp only [show 446#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls0.source072 D hash (s00 s) 1#usize 1952#usize 446#u32 0#usize (by decide)
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
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s01 s).«at» 1984#usize)=ok (encodeState (JGc_TX2_HashBytes.state [208,106,137,156,88,252,163,167,103,236,35,6,239,195,55,37,126,226,113,63,72,148,131,98,39,186,94,170,101,28,78,97])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 61
      5216#usize 1952#usize 1984#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings05.k0c061_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes0 1#usize 1#usize 2#usize 1984#usize 3264#usize
    664#u32 (encodeState value061) (encodeState (JGc_TX2_HashBytes.state [208,106,137,156,88,252,163,167,103,236,35,6,239,195,55,37,126,226,113,63,72,148,131,98,39,186,94,170,101,28,78,97])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read01
  simp only [show 664#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes0 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls0.source073 D hash (s01 s) 2#usize 1984#usize 664#u32 1#usize (by decide)
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
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s02 s).«at» 2016#usize)=ok (encodeState (JGc_TX2_HashBytes.state [96,86,165,214,60,58,153,79,245,118,213,70,119,212,97,94,73,218,75,178,144,237,239,5,152,168,50,70,114,194,196,190])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 62
      5216#usize 1984#usize 2016#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings05.k0c062_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes0 2#usize 2#usize 3#usize 2016#usize 3232#usize
    1317#u32 (encodeState value062) (encodeState (JGc_TX2_HashBytes.state [96,86,165,214,60,58,153,79,245,118,213,70,119,212,97,94,73,218,75,178,144,237,239,5,152,168,50,70,114,194,196,190])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read02
  simp only [show 1317#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes0 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls0.source074 D hash (s02 s) 3#usize 2016#usize 1317#u32 2#usize (by decide)
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
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s03 s).«at» 2048#usize)=ok (encodeState (JGc_TX2_HashBytes.state [67,56,172,155,250,179,222,134,219,90,202,255,153,121,98,56,144,27,144,127,45,183,122,190,111,165,244,250,51,94,26,214])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 63
      5216#usize 2016#usize 2048#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings05.k0c063_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes0 3#usize 3#usize 4#usize 2048#usize 3200#usize
    1730#u32 (encodeState value063) (encodeState (JGc_TX2_HashBytes.state [67,56,172,155,250,179,222,134,219,90,202,255,153,121,98,56,144,27,144,127,45,183,122,190,111,165,244,250,51,94,26,214])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read03
  simp only [show 1730#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes0 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls0.source075 D hash (s03 s) 4#usize 2048#usize 1730#u32 3#usize (by decide)
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
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s04 s).«at» 2080#usize)=ok (encodeState (JGc_TX2_HashBytes.state [137,230,227,165,233,42,125,178,96,86,175,162,161,211,230,12,211,67,26,123,39,21,192,98,16,164,106,28,9,61,16,102])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 64
      5216#usize 2048#usize 2080#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings05.k0c064_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes0 4#usize 4#usize 5#usize 2080#usize 3168#usize
    1995#u32 (encodeState value064) (encodeState (JGc_TX2_HashBytes.state [137,230,227,165,233,42,125,178,96,86,175,162,161,211,230,12,211,67,26,123,39,21,192,98,16,164,106,28,9,61,16,102])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read04
  simp only [show 1995#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes0 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls0.source076 D hash (s04 s) 5#usize 2080#usize 1995#u32 4#usize (by decide)
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
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s05 s).«at» 2112#usize)=ok (encodeState (JGc_TX2_HashBytes.state [63,8,57,60,116,219,77,27,90,202,240,19,201,3,4,1,44,37,168,199,67,205,148,46,190,34,185,150,152,219,190,185])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 65
      5216#usize 2080#usize 2112#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings05.k0c065_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes0 5#usize 5#usize 6#usize 2112#usize 3136#usize
    4136#u32 (encodeState value065) (encodeState (JGc_TX2_HashBytes.state [63,8,57,60,116,219,77,27,90,202,240,19,201,3,4,1,44,37,168,199,67,205,148,46,190,34,185,150,152,219,190,185])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read05
  simp only [show 4136#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes0 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls0.source077 D hash (s05 s) 6#usize 2112#usize 4136#u32 5#usize (by decide)
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
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s06 s).«at» 2144#usize)=ok (encodeState (JGc_TX2_HashBytes.state [40,148,151,234,47,81,210,205,168,84,182,75,116,195,24,72,138,16,180,55,51,82,30,80,248,67,3,180,153,50,12,9])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 66
      5216#usize 2112#usize 2144#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings05.k0c066_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes0 6#usize 6#usize 7#usize 2144#usize 3104#usize
    4675#u32 (encodeState value066) (encodeState (JGc_TX2_HashBytes.state [40,148,151,234,47,81,210,205,168,84,182,75,116,195,24,72,138,16,180,55,51,82,30,80,248,67,3,180,153,50,12,9])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read06
  simp only [show 4675#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes0 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls0.source078 D hash (s06 s) 7#usize 2144#usize 4675#u32 6#usize (by decide)
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
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s07 s).«at» 2176#usize)=ok (encodeState (JGc_TX2_HashBytes.state [226,33,86,10,93,130,74,210,30,96,38,232,163,178,202,190,106,193,115,33,153,59,158,30,27,85,135,153,164,154,213,23])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 67
      5216#usize 2144#usize 2176#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings05.k0c067_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes0 7#usize 7#usize 8#usize 2176#usize 3072#usize
    5192#u32 (encodeState value067) (encodeState (JGc_TX2_HashBytes.state [226,33,86,10,93,130,74,210,30,96,38,232,163,178,202,190,106,193,115,33,153,59,158,30,27,85,135,153,164,154,213,23])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read07
  simp only [show 5192#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes0 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls0.source079 D hash (s07 s) 8#usize 2176#usize 5192#u32 7#usize (by decide)
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
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s08 s).«at» 2208#usize)=ok (encodeState (JGc_TX2_HashBytes.state [129,93,233,4,10,237,255,49,97,128,241,124,80,41,207,190,126,211,126,91,31,193,143,89,254,222,118,216,114,175,42,17])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 68
      5216#usize 2176#usize 2208#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings05.k0c068_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes0 8#usize 8#usize 9#usize 2208#usize 3040#usize
    5565#u32 (encodeState value068) (encodeState (JGc_TX2_HashBytes.state [129,93,233,4,10,237,255,49,97,128,241,124,80,41,207,190,126,211,126,91,31,193,143,89,254,222,118,216,114,175,42,17])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read08
  simp only [show 5565#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes0 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls0.source080 D hash (s08 s) 9#usize 2208#usize 5565#u32 8#usize (by decide)
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
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s09 s).«at» 2240#usize)=ok (encodeState (JGc_TX2_HashBytes.state [22,71,7,19,51,149,73,150,190,170,30,203,179,236,91,204,95,54,245,160,239,72,74,49,49,87,24,43,131,42,87,52])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 69
      5216#usize 2208#usize 2240#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings05.k0c069_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes0 9#usize 9#usize 10#usize 2240#usize 3008#usize
    5613#u32 (encodeState value069) (encodeState (JGc_TX2_HashBytes.state [22,71,7,19,51,149,73,150,190,170,30,203,179,236,91,204,95,54,245,160,239,72,74,49,49,87,24,43,131,42,87,52])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read09
  simp only [show 5613#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes0 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls0.source081 D hash (s09 s) 10#usize 2240#usize 5613#u32 9#usize (by decide)
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
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s10 s).«at» 2272#usize)=ok (encodeState (JGc_TX2_HashBytes.state [199,10,148,235,137,56,26,21,42,164,55,2,116,225,94,53,71,47,166,136,132,254,119,246,161,220,161,87,230,45,113,199])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 70
      5216#usize 2240#usize 2272#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings05.k0c070_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes0 10#usize 10#usize 11#usize 2272#usize 2976#usize
    5801#u32 (encodeState value070) (encodeState (JGc_TX2_HashBytes.state [199,10,148,235,137,56,26,21,42,164,55,2,116,225,94,53,71,47,166,136,132,254,119,246,161,220,161,87,230,45,113,199])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read10
  simp only [show 5801#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes0 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls0.source082 D hash (s10 s) 11#usize 2272#usize 5801#u32 10#usize (by decide)
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
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s11 s).«at» 2304#usize)=ok (encodeState (JGc_TX2_HashBytes.state [72,241,117,171,183,245,182,47,99,0,248,6,146,198,34,85,212,4,80,93,238,61,89,145,106,182,22,198,155,40,28,141])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 71
      5216#usize 2272#usize 2304#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings05.k0c071_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes0 11#usize 11#usize 12#usize 2304#usize 2944#usize
    6815#u32 (encodeState value071) (encodeState (JGc_TX2_HashBytes.state [72,241,117,171,183,245,182,47,99,0,248,6,146,198,34,85,212,4,80,93,238,61,89,145,106,182,22,198,155,40,28,141])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read11
  simp only [show 6815#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes0 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls0.source083 D hash (s11 s) 12#usize 2304#usize 6815#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 2304 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 2272 v11
      6815#u32 11#usize (encodeState value083) 2304#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGm_TX2_Supplied.nodes0 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGm_TX2_Supplied.nodes0 1#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGm_TX2_Supplied.nodes0 2#usize 2#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGm_TX2_Supplied.nodes0 3#usize 3#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGm_TX2_Supplied.nodes0 4#usize 4#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGm_TX2_Supplied.nodes0 5#usize 5#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGm_TX2_Supplied.nodes0 6#usize 6#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGm_TX2_Supplied.nodes0 7#usize 7#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGm_TX2_Supplied.nodes0 8#usize 8#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGm_TX2_Supplied.nodes0 9#usize 9#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGm_TX2_Supplied.nodes0 10#usize 10#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s) JGm_TX2_Supplied.nodes0 11#usize 11#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active10 row10
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s12 s) JGm_TX2_Supplied.nodes0 12#usize 12#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active11 row11
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s12 s).n.val≤12;rw [v12.size];decide)
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 2304
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level0_05
end
