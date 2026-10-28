import NDO_JGm_TX2_ParentCalls1
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level1_06
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGh_TX2_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes1
def indices00 : List U32 := [223#u32,332#u32,658#u32,865#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
def values00 : List (Array U8 32#usize) := [encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 223#u32 0#usize (encodeState value084) 2336#usize
 def indices01 : List U32 := [111#u32,332#u32,658#u32,865#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value084,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 332#u32 1#usize (encodeState value085) 2368#usize
 def indices02 : List U32 := [111#u32,166#u32,658#u32,865#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 658#u32 2#usize (encodeState value086) 2400#usize
 def indices03 : List U32 := [111#u32,166#u32,329#u32,865#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 865#u32 3#usize (encodeState value087) 2432#usize
 def indices04 : List U32 := [111#u32,166#u32,329#u32,432#u32,997#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 997#u32 4#usize (encodeState value088) 2464#usize
 def indices05 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,2068#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 2068#u32 5#usize (encodeState value089) 2496#usize
 def indices06 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,2337#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 2337#u32 6#usize (encodeState value090) 2528#usize
 def indices07 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,2596#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 2596#u32 7#usize (encodeState value091) 2560#usize
 def indices08 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,2782#u32,2806#u32,2900#u32,3407#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 2782#u32 8#usize (encodeState value092) 2592#usize
 def indices09 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,2806#u32,2900#u32,3407#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value081,encodeState value082,encodeState value083]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 2806#u32 9#usize (encodeState value093) 2624#usize
 def indices10 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,1403#u32,2900#u32,3407#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value082,encodeState value083]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 2900#u32 10#usize (encodeState value094) 2656#usize
 def indices11 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,1403#u32,1450#u32,3407#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value083]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 3407#u32 11#usize (encodeState value095) 2688#usize
 def indices12 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,1403#u32,1450#u32,1703#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,1403#u32,1450#u32,1703#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 2304) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 2688 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 2304 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 223#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 2304 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value072) :=
    JGm_TX2_View.value (s00 s) indices00 values00 2304 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=2304#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠223#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨332#u32,JGm_TX2_View.index (s00 s) indices00 values00 2304 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s00 s).«at» 2336#usize)=ok (encodeState (JGc_TX2_HashBytes.state [5,14,141,90,169,39,53,83,83,142,81,208,146,23,21,216,91,232,81,120,231,229,168,131,104,135,53,201,168,191,194,47])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 72
      5216#usize 2304#usize 2336#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings06.k1c072_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes1 0#usize 0#usize 1#usize 2336#usize 2912#usize
    223#u32 (encodeState value072) (encodeState (JGc_TX2_HashBytes.state [5,14,141,90,169,39,53,83,83,142,81,208,146,23,21,216,91,232,81,120,231,229,168,131,104,135,53,201,168,191,194,47])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read00
  simp only [show 223#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls1.source084 D hash (s00 s) 1#usize 2336#usize 223#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 2336 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 2304 v00
      223#u32 0#usize (encodeState value084) 2336#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 332#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 2336 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value073) :=
    JGm_TX2_View.value (s01 s) indices01 values01 2336 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=2336#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠332#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨658#u32,JGm_TX2_View.index (s01 s) indices01 values01 2336 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s01 s).«at» 2368#usize)=ok (encodeState (JGc_TX2_HashBytes.state [184,111,36,183,104,91,22,115,84,207,81,116,150,195,194,158,38,199,21,130,103,36,190,232,127,29,217,213,102,104,132,241])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 73
      5216#usize 2336#usize 2368#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings06.k1c073_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes1 1#usize 1#usize 2#usize 2368#usize 2880#usize
    332#u32 (encodeState value073) (encodeState (JGc_TX2_HashBytes.state [184,111,36,183,104,91,22,115,84,207,81,116,150,195,194,158,38,199,21,130,103,36,190,232,127,29,217,213,102,104,132,241])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read01
  simp only [show 332#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls1.source085 D hash (s01 s) 2#usize 2368#usize 332#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 2368 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 2336 v01
      332#u32 1#usize (encodeState value085) 2368#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 658#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 2368 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value074) :=
    JGm_TX2_View.value (s02 s) indices02 values02 2368 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=2368#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠658#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨865#u32,JGm_TX2_View.index (s02 s) indices02 values02 2368 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s02 s).«at» 2400#usize)=ok (encodeState (JGc_TX2_HashBytes.state [153,177,65,71,52,128,250,203,189,12,49,80,141,229,145,210,198,229,202,31,188,162,195,192,31,215,14,0,126,110,162,251])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 74
      5216#usize 2368#usize 2400#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings06.k1c074_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes1 2#usize 2#usize 3#usize 2400#usize 2848#usize
    658#u32 (encodeState value074) (encodeState (JGc_TX2_HashBytes.state [153,177,65,71,52,128,250,203,189,12,49,80,141,229,145,210,198,229,202,31,188,162,195,192,31,215,14,0,126,110,162,251])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read02
  simp only [show 658#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls1.source086 D hash (s02 s) 3#usize 2400#usize 658#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 2400 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 2368 v02
      658#u32 2#usize (encodeState value086) 2400#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 865#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 2400 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value075) :=
    JGm_TX2_View.value (s03 s) indices03 values03 2400 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=2400#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠865#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨997#u32,JGm_TX2_View.index (s03 s) indices03 values03 2400 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s03 s).«at» 2432#usize)=ok (encodeState (JGc_TX2_HashBytes.state [55,53,215,205,196,229,228,81,145,6,28,131,82,169,210,238,87,109,105,13,169,125,241,37,3,56,148,106,32,161,232,37])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 75
      5216#usize 2400#usize 2432#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings06.k1c075_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes1 3#usize 3#usize 4#usize 2432#usize 2816#usize
    865#u32 (encodeState value075) (encodeState (JGc_TX2_HashBytes.state [55,53,215,205,196,229,228,81,145,6,28,131,82,169,210,238,87,109,105,13,169,125,241,37,3,56,148,106,32,161,232,37])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read03
  simp only [show 865#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls1.source087 D hash (s03 s) 4#usize 2432#usize 865#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 2432 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 2400 v03
      865#u32 3#usize (encodeState value087) 2432#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 997#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 2432 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value076) :=
    JGm_TX2_View.value (s04 s) indices04 values04 2432 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=2432#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠997#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2068#u32,JGm_TX2_View.index (s04 s) indices04 values04 2432 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s04 s).«at» 2464#usize)=ok (encodeState (JGc_TX2_HashBytes.state [6,3,24,53,73,183,202,184,64,100,52,173,74,76,36,231,30,127,112,238,69,229,58,35,76,128,165,168,59,82,19,143])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 76
      5216#usize 2432#usize 2464#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings06.k1c076_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes1 4#usize 4#usize 5#usize 2464#usize 2784#usize
    997#u32 (encodeState value076) (encodeState (JGc_TX2_HashBytes.state [6,3,24,53,73,183,202,184,64,100,52,173,74,76,36,231,30,127,112,238,69,229,58,35,76,128,165,168,59,82,19,143])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read04
  simp only [show 997#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls1.source088 D hash (s04 s) 5#usize 2464#usize 997#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 2464 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 2432 v04
      997#u32 4#usize (encodeState value088) 2464#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 2068#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 2464 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value077) :=
    JGm_TX2_View.value (s05 s) indices05 values05 2464 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=2464#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠2068#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2337#u32,JGm_TX2_View.index (s05 s) indices05 values05 2464 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s05 s).«at» 2496#usize)=ok (encodeState (JGc_TX2_HashBytes.state [182,208,30,198,94,243,210,10,44,105,105,195,118,197,107,41,213,138,210,114,164,7,16,25,109,205,12,9,192,79,131,42])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 77
      5216#usize 2464#usize 2496#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings06.k1c077_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes1 5#usize 5#usize 6#usize 2496#usize 2752#usize
    2068#u32 (encodeState value077) (encodeState (JGc_TX2_HashBytes.state [182,208,30,198,94,243,210,10,44,105,105,195,118,197,107,41,213,138,210,114,164,7,16,25,109,205,12,9,192,79,131,42])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read05
  simp only [show 2068#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls1.source089 D hash (s05 s) 6#usize 2496#usize 2068#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 2496 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 2464 v05
      2068#u32 5#usize (encodeState value089) 2496#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 2337#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 2496 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value078) :=
    JGm_TX2_View.value (s06 s) indices06 values06 2496 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=2496#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠2337#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2596#u32,JGm_TX2_View.index (s06 s) indices06 values06 2496 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s06 s).«at» 2528#usize)=ok (encodeState (JGc_TX2_HashBytes.state [156,230,140,61,84,248,80,66,2,44,182,101,147,148,190,86,151,50,143,164,104,178,90,105,127,41,40,98,219,204,233,208])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 78
      5216#usize 2496#usize 2528#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings06.k1c078_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes1 6#usize 6#usize 7#usize 2528#usize 2720#usize
    2337#u32 (encodeState value078) (encodeState (JGc_TX2_HashBytes.state [156,230,140,61,84,248,80,66,2,44,182,101,147,148,190,86,151,50,143,164,104,178,90,105,127,41,40,98,219,204,233,208])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read06
  simp only [show 2337#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls1.source090 D hash (s06 s) 7#usize 2528#usize 2337#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 2528 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 2496 v06
      2337#u32 6#usize (encodeState value090) 2528#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 2596#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 2528 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value079) :=
    JGm_TX2_View.value (s07 s) indices07 values07 2528 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=2528#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠2596#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2782#u32,JGm_TX2_View.index (s07 s) indices07 values07 2528 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s07 s).«at» 2560#usize)=ok (encodeState (JGc_TX2_HashBytes.state [54,100,128,13,24,149,127,139,9,65,12,226,120,23,178,22,196,33,176,221,226,100,237,14,131,43,117,52,127,107,94,226])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 79
      5216#usize 2528#usize 2560#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings06.k1c079_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes1 7#usize 7#usize 8#usize 2560#usize 2688#usize
    2596#u32 (encodeState value079) (encodeState (JGc_TX2_HashBytes.state [54,100,128,13,24,149,127,139,9,65,12,226,120,23,178,22,196,33,176,221,226,100,237,14,131,43,117,52,127,107,94,226])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read07
  simp only [show 2596#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls1.source091 D hash (s07 s) 8#usize 2560#usize 2596#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 2560 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 2528 v07
      2596#u32 7#usize (encodeState value091) 2560#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 2782#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 2560 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value080) :=
    JGm_TX2_View.value (s08 s) indices08 values08 2560 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=2560#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠2782#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2806#u32,JGm_TX2_View.index (s08 s) indices08 values08 2560 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s08 s).«at» 2592#usize)=ok (encodeState (JGc_TX2_HashBytes.state [149,218,98,173,65,74,136,31,78,43,246,179,253,13,41,169,136,128,238,86,77,188,190,151,31,19,131,60,219,216,14,8])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 80
      5216#usize 2560#usize 2592#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings06.k1c080_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes1 8#usize 8#usize 9#usize 2592#usize 2656#usize
    2782#u32 (encodeState value080) (encodeState (JGc_TX2_HashBytes.state [149,218,98,173,65,74,136,31,78,43,246,179,253,13,41,169,136,128,238,86,77,188,190,151,31,19,131,60,219,216,14,8])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read08
  simp only [show 2782#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls1.source092 D hash (s08 s) 9#usize 2592#usize 2782#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 2592 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 2560 v08
      2782#u32 8#usize (encodeState value092) 2592#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 2806#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 2592 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value081) :=
    JGm_TX2_View.value (s09 s) indices09 values09 2592 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=2592#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠2806#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2900#u32,JGm_TX2_View.index (s09 s) indices09 values09 2592 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s09 s).«at» 2624#usize)=ok (encodeState (JGc_TX2_HashBytes.state [185,22,26,113,55,154,122,202,166,55,107,15,192,104,169,93,232,7,36,110,64,109,92,228,35,195,207,119,200,145,218,42])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 81
      5216#usize 2592#usize 2624#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings06.k1c081_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes1 9#usize 9#usize 10#usize 2624#usize 2624#usize
    2806#u32 (encodeState value081) (encodeState (JGc_TX2_HashBytes.state [185,22,26,113,55,154,122,202,166,55,107,15,192,104,169,93,232,7,36,110,64,109,92,228,35,195,207,119,200,145,218,42])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read09
  simp only [show 2806#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls1.source093 D hash (s09 s) 10#usize 2624#usize 2806#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 2624 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 2592 v09
      2806#u32 9#usize (encodeState value093) 2624#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 2900#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 2624 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value082) :=
    JGm_TX2_View.value (s10 s) indices10 values10 2624 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=2624#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠2900#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨3407#u32,JGm_TX2_View.index (s10 s) indices10 values10 2624 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s10 s).«at» 2656#usize)=ok (encodeState (JGc_TX2_HashBytes.state [1,22,169,204,229,7,149,73,247,171,17,240,135,153,232,96,139,106,201,197,27,100,247,82,26,95,83,98,253,103,75,161])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 82
      5216#usize 2624#usize 2656#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings06.k1c082_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes1 10#usize 10#usize 11#usize 2656#usize 2592#usize
    2900#u32 (encodeState value082) (encodeState (JGc_TX2_HashBytes.state [1,22,169,204,229,7,149,73,247,171,17,240,135,153,232,96,139,106,201,197,27,100,247,82,26,95,83,98,253,103,75,161])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read10
  simp only [show 2900#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes1 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls1.source094 D hash (s10 s) 11#usize 2656#usize 2900#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 2656 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 2624 v10
      2900#u32 10#usize (encodeState value094) 2656#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 3407#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 2656 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value083) :=
    JGm_TX2_View.value (s11 s) indices11 values11 2656 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=2656#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠3407#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s11 s).«at» 2688#usize)=ok (encodeState (JGc_TX2_HashBytes.state [50,104,161,78,130,249,84,55,40,90,205,163,184,100,156,233,175,243,38,61,50,107,155,242,21,74,218,247,171,43,165,196])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 83
      5216#usize 2656#usize 2688#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings06.k1c083_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes1 11#usize 11#usize 12#usize 2688#usize 2560#usize
    3407#u32 (encodeState value083) (encodeState (JGc_TX2_HashBytes.state [50,104,161,78,130,249,84,55,40,90,205,163,184,100,156,233,175,243,38,61,50,107,155,242,21,74,218,247,171,43,165,196])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read11
  simp only [show 3407#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes1 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls1.source095 D hash (s11 s) 12#usize 2688#usize 3407#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 2688 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 2656 v11
      3407#u32 11#usize (encodeState value095) 2688#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 2688
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level1_06
end
