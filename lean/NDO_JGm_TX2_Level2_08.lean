import NDO_JGm_TX2_ParentCalls2
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level2_08
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGc_TX2_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes2
def indices00 : List U32 := [13#u32,20#u32,41#u32,54#u32,62#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
def values00 : List (Array U8 32#usize) := [encodeState value096,encodeState value097,encodeState value098,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 13#u32 0#usize (encodeState value108) 3104#usize
 def indices01 : List U32 := [6#u32,20#u32,41#u32,54#u32,62#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value108,encodeState value097,encodeState value098,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 20#u32 1#usize (encodeState value109) 3136#usize
 def indices02 : List U32 := [6#u32,10#u32,41#u32,54#u32,62#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value098,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 41#u32 2#usize (encodeState value110) 3168#usize
 def indices03 : List U32 := [6#u32,10#u32,20#u32,54#u32,62#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 54#u32 3#usize (encodeState value111) 3200#usize
 def indices04 : List U32 := [6#u32,10#u32,20#u32,27#u32,62#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 62#u32 4#usize (encodeState value112) 3232#usize
 def indices05 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 129#u32 5#usize (encodeState value113) 3264#usize
 def indices06 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 146#u32 6#usize (encodeState value114) 3296#usize
 def indices07 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 162#u32 7#usize (encodeState value115) 3328#usize
 def indices08 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,173#u32,175#u32,181#u32,212#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 173#u32 8#usize (encodeState value116) 3360#usize
 def indices09 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,175#u32,181#u32,212#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value105,encodeState value106,encodeState value107]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 175#u32 9#usize (encodeState value117) 3392#usize
 def indices10 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,181#u32,212#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value106,encodeState value107]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 181#u32 10#usize (encodeState value118) 3424#usize
 def indices11 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,212#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value107]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 212#u32 11#usize (encodeState value119) 3456#usize
 def indices12 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3072) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3456 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3072 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 13#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3072 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value096) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3072 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3072#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠13#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨20#u32,JGm_TX2_View.index (s00 s) indices00 values00 3072 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s00 s).«at» 3104#usize)=ok (encodeState (JGc_TX2_HashBytes.state [218,238,50,200,63,122,205,112,1,96,129,225,174,219,13,23,105,209,62,106,22,187,3,131,78,242,137,23,141,221,53,36])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 96
      4512#usize 3072#usize 3104#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings08.k2c096_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes2 0#usize 0#usize 1#usize 3104#usize 1440#usize
    13#u32 (encodeState value096) (encodeState (JGc_TX2_HashBytes.state [218,238,50,200,63,122,205,112,1,96,129,225,174,219,13,23,105,209,62,106,22,187,3,131,78,242,137,23,141,221,53,36])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read00
  simp only [show 13#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls2.source108 D hash (s00 s) 1#usize 3104#usize 13#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3104 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3072 v00
      13#u32 0#usize (encodeState value108) 3104#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 20#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 3104 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value097) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3104 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=3104#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠20#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨41#u32,JGm_TX2_View.index (s01 s) indices01 values01 3104 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s01 s).«at» 3136#usize)=ok (encodeState (JGc_TX2_HashBytes.state [15,122,10,55,6,140,91,132,57,151,30,131,87,72,204,232,62,161,26,173,137,221,84,100,227,254,29,235,65,221,129,22])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 97
      4512#usize 3104#usize 3136#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings08.k2c097_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes2 1#usize 1#usize 2#usize 3136#usize 1408#usize
    20#u32 (encodeState value097) (encodeState (JGc_TX2_HashBytes.state [15,122,10,55,6,140,91,132,57,151,30,131,87,72,204,232,62,161,26,173,137,221,84,100,227,254,29,235,65,221,129,22])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read01
  simp only [show 20#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls2.source109 D hash (s01 s) 2#usize 3136#usize 20#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 3136 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 3104 v01
      20#u32 1#usize (encodeState value109) 3136#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 41#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 3136 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value098) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3136 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=3136#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠41#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨54#u32,JGm_TX2_View.index (s02 s) indices02 values02 3136 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s02 s).«at» 3168#usize)=ok (encodeState (JGc_TX2_HashBytes.state [11,224,123,69,59,20,49,235,7,135,199,210,67,32,45,15,0,196,88,133,47,103,208,79,73,87,177,173,105,72,84,224])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 98
      4512#usize 3136#usize 3168#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings08.k2c098_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes2 2#usize 2#usize 3#usize 3168#usize 1376#usize
    41#u32 (encodeState value098) (encodeState (JGc_TX2_HashBytes.state [11,224,123,69,59,20,49,235,7,135,199,210,67,32,45,15,0,196,88,133,47,103,208,79,73,87,177,173,105,72,84,224])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read02
  simp only [show 41#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls2.source110 D hash (s02 s) 3#usize 3168#usize 41#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 3168 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 3136 v02
      41#u32 2#usize (encodeState value110) 3168#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 54#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 3168 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value099) :=
    JGm_TX2_View.value (s03 s) indices03 values03 3168 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=3168#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠54#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨62#u32,JGm_TX2_View.index (s03 s) indices03 values03 3168 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s03 s).«at» 3200#usize)=ok (encodeState (JGc_TX2_HashBytes.state [129,102,155,34,234,81,11,95,91,233,175,252,151,74,152,169,180,251,141,65,54,179,76,165,27,19,131,34,207,116,53,222])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 99
      4512#usize 3168#usize 3200#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings08.k2c099_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes2 3#usize 3#usize 4#usize 3200#usize 1344#usize
    54#u32 (encodeState value099) (encodeState (JGc_TX2_HashBytes.state [129,102,155,34,234,81,11,95,91,233,175,252,151,74,152,169,180,251,141,65,54,179,76,165,27,19,131,34,207,116,53,222])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read03
  simp only [show 54#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes2 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls2.source111 D hash (s03 s) 4#usize 3200#usize 54#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 3200 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 3168 v03
      54#u32 3#usize (encodeState value111) 3200#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 62#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 3200 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value100) :=
    JGm_TX2_View.value (s04 s) indices04 values04 3200 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=3200#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠62#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨129#u32,JGm_TX2_View.index (s04 s) indices04 values04 3200 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s04 s).«at» 3232#usize)=ok (encodeState (JGc_TX2_HashBytes.state [223,15,252,170,76,199,28,197,19,110,150,124,50,238,246,246,53,155,152,179,125,169,80,124,193,41,198,224,244,251,125,62])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 100
      4512#usize 3200#usize 3232#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings08.k2c100_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes2 4#usize 4#usize 5#usize 3232#usize 1312#usize
    62#u32 (encodeState value100) (encodeState (JGc_TX2_HashBytes.state [223,15,252,170,76,199,28,197,19,110,150,124,50,238,246,246,53,155,152,179,125,169,80,124,193,41,198,224,244,251,125,62])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read04
  simp only [show 62#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes2 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls2.source112 D hash (s04 s) 5#usize 3232#usize 62#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 3232 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 3200 v04
      62#u32 4#usize (encodeState value112) 3232#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 129#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 3232 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value101) :=
    JGm_TX2_View.value (s05 s) indices05 values05 3232 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=3232#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠129#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨146#u32,JGm_TX2_View.index (s05 s) indices05 values05 3232 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s05 s).«at» 3264#usize)=ok (encodeState (JGc_TX2_HashBytes.state [161,6,62,173,199,189,101,43,53,128,167,220,181,53,132,29,233,225,141,96,8,197,157,60,39,57,32,29,141,203,158,0])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 101
      4512#usize 3232#usize 3264#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings08.k2c101_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes2 5#usize 5#usize 6#usize 3264#usize 1280#usize
    129#u32 (encodeState value101) (encodeState (JGc_TX2_HashBytes.state [161,6,62,173,199,189,101,43,53,128,167,220,181,53,132,29,233,225,141,96,8,197,157,60,39,57,32,29,141,203,158,0])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read05
  simp only [show 129#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes2 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls2.source113 D hash (s05 s) 6#usize 3264#usize 129#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 3264 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 3232 v05
      129#u32 5#usize (encodeState value113) 3264#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 146#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 3264 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value102) :=
    JGm_TX2_View.value (s06 s) indices06 values06 3264 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=3264#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠146#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨162#u32,JGm_TX2_View.index (s06 s) indices06 values06 3264 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s06 s).«at» 3296#usize)=ok (encodeState (JGc_TX2_HashBytes.state [32,61,232,250,65,134,84,127,55,144,151,156,243,30,160,217,254,133,111,178,149,51,211,242,194,156,234,13,169,205,98,129])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 102
      4512#usize 3264#usize 3296#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings08.k2c102_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes2 6#usize 6#usize 7#usize 3296#usize 1248#usize
    146#u32 (encodeState value102) (encodeState (JGc_TX2_HashBytes.state [32,61,232,250,65,134,84,127,55,144,151,156,243,30,160,217,254,133,111,178,149,51,211,242,194,156,234,13,169,205,98,129])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read06
  simp only [show 146#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes2 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls2.source114 D hash (s06 s) 7#usize 3296#usize 146#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 3296 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 3264 v06
      146#u32 6#usize (encodeState value114) 3296#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 162#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 3296 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value103) :=
    JGm_TX2_View.value (s07 s) indices07 values07 3296 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=3296#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠162#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨173#u32,JGm_TX2_View.index (s07 s) indices07 values07 3296 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s07 s).«at» 3328#usize)=ok (encodeState (JGc_TX2_HashBytes.state [195,142,70,165,83,234,237,242,133,12,38,244,175,89,218,59,200,75,178,84,82,144,239,11,186,168,39,120,171,157,103,50])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 103
      4512#usize 3296#usize 3328#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings08.k2c103_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes2 7#usize 7#usize 8#usize 3328#usize 1216#usize
    162#u32 (encodeState value103) (encodeState (JGc_TX2_HashBytes.state [195,142,70,165,83,234,237,242,133,12,38,244,175,89,218,59,200,75,178,84,82,144,239,11,186,168,39,120,171,157,103,50])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read07
  simp only [show 162#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes2 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls2.source115 D hash (s07 s) 8#usize 3328#usize 162#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 3328 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 3296 v07
      162#u32 7#usize (encodeState value115) 3328#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 173#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 3328 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value104) :=
    JGm_TX2_View.value (s08 s) indices08 values08 3328 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=3328#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠173#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨175#u32,JGm_TX2_View.index (s08 s) indices08 values08 3328 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s08 s).«at» 3360#usize)=ok (encodeState (JGc_TX2_HashBytes.state [120,246,194,40,100,13,43,67,172,255,221,65,73,215,185,58,140,17,192,106,47,103,7,109,141,22,236,224,213,222,56,35])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 104
      4512#usize 3328#usize 3360#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings08.k2c104_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes2 8#usize 8#usize 9#usize 3360#usize 1184#usize
    173#u32 (encodeState value104) (encodeState (JGc_TX2_HashBytes.state [120,246,194,40,100,13,43,67,172,255,221,65,73,215,185,58,140,17,192,106,47,103,7,109,141,22,236,224,213,222,56,35])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read08
  simp only [show 173#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes2 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls2.source116 D hash (s08 s) 9#usize 3360#usize 173#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 3360 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 3328 v08
      173#u32 8#usize (encodeState value116) 3360#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 175#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 3360 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value105) :=
    JGm_TX2_View.value (s09 s) indices09 values09 3360 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=3360#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠175#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨181#u32,JGm_TX2_View.index (s09 s) indices09 values09 3360 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s09 s).«at» 3392#usize)=ok (encodeState (JGc_TX2_HashBytes.state [68,26,85,81,72,216,142,241,226,107,88,198,11,13,123,131,251,67,93,136,104,115,251,44,204,2,192,72,144,92,14,90])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 105
      4512#usize 3360#usize 3392#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings08.k2c105_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes2 9#usize 9#usize 10#usize 3392#usize 1152#usize
    175#u32 (encodeState value105) (encodeState (JGc_TX2_HashBytes.state [68,26,85,81,72,216,142,241,226,107,88,198,11,13,123,131,251,67,93,136,104,115,251,44,204,2,192,72,144,92,14,90])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read09
  simp only [show 175#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes2 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls2.source117 D hash (s09 s) 10#usize 3392#usize 175#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 3392 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 3360 v09
      175#u32 9#usize (encodeState value117) 3392#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 181#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 3392 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value106) :=
    JGm_TX2_View.value (s10 s) indices10 values10 3392 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=3392#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠181#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨212#u32,JGm_TX2_View.index (s10 s) indices10 values10 3392 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s10 s).«at» 3424#usize)=ok (encodeState (JGc_TX2_HashBytes.state [124,231,161,169,115,69,108,68,119,53,3,24,134,43,151,144,104,169,143,201,144,171,181,140,24,93,179,174,204,97,196,133])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 106
      4512#usize 3392#usize 3424#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings08.k2c106_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes2 10#usize 10#usize 11#usize 3424#usize 1120#usize
    181#u32 (encodeState value106) (encodeState (JGc_TX2_HashBytes.state [124,231,161,169,115,69,108,68,119,53,3,24,134,43,151,144,104,169,143,201,144,171,181,140,24,93,179,174,204,97,196,133])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read10
  simp only [show 181#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes2 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls2.source118 D hash (s10 s) 11#usize 3424#usize 181#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 3424 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 3392 v10
      181#u32 10#usize (encodeState value118) 3424#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 212#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 3424 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value107) :=
    JGm_TX2_View.value (s11 s) indices11 values11 3424 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=3424#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠212#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s11 s).«at» 3456#usize)=ok (encodeState (JGc_TX2_HashBytes.state [196,46,232,194,162,166,36,191,104,15,74,199,133,171,182,35,139,73,145,24,71,236,91,2,23,6,247,180,55,217,53,89])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 107
      4512#usize 3424#usize 3456#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings08.k2c107_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes2 11#usize 11#usize 12#usize 3456#usize 1088#usize
    212#u32 (encodeState value107) (encodeState (JGc_TX2_HashBytes.state [196,46,232,194,162,166,36,191,104,15,74,199,133,171,182,35,139,73,145,24,71,236,91,2,23,6,247,180,55,217,53,89])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read11
  simp only [show 212#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes2 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls2.source119 D hash (s11 s) 12#usize 3456#usize 212#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 3456 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 3424 v11
      212#u32 11#usize (encodeState value119) 3456#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 3456
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level2_08
end
