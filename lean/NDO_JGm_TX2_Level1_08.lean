import NDO_JGm_TX2_ParentCalls1
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level1_08
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGh_TX2_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes1
def indices00 : List U32 := [55#u32,83#u32,164#u32,216#u32,249#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
def values00 : List (Array U8 32#usize) := [encodeState value096,encodeState value097,encodeState value098,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 55#u32 0#usize (encodeState value108) 3104#usize
 def indices01 : List U32 := [27#u32,83#u32,164#u32,216#u32,249#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value108,encodeState value097,encodeState value098,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 83#u32 1#usize (encodeState value109) 3136#usize
 def indices02 : List U32 := [27#u32,41#u32,164#u32,216#u32,249#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value098,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 164#u32 2#usize (encodeState value110) 3168#usize
 def indices03 : List U32 := [27#u32,41#u32,82#u32,216#u32,249#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 216#u32 3#usize (encodeState value111) 3200#usize
 def indices04 : List U32 := [27#u32,41#u32,82#u32,108#u32,249#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 249#u32 4#usize (encodeState value112) 3232#usize
 def indices05 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 517#u32 5#usize (encodeState value113) 3264#usize
 def indices06 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 584#u32 6#usize (encodeState value114) 3296#usize
 def indices07 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 649#u32 7#usize (encodeState value115) 3328#usize
 def indices08 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,695#u32,701#u32,725#u32,851#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 695#u32 8#usize (encodeState value116) 3360#usize
 def indices09 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,347#u32,701#u32,725#u32,851#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value105,encodeState value106,encodeState value107]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 701#u32 9#usize (encodeState value117) 3392#usize
 def indices10 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,347#u32,350#u32,725#u32,851#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value106,encodeState value107]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 725#u32 10#usize (encodeState value118) 3424#usize
 def indices11 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,347#u32,350#u32,362#u32,851#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value107]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 851#u32 11#usize (encodeState value119) 3456#usize
 def indices12 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,347#u32,350#u32,362#u32,425#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,347#u32,350#u32,362#u32,425#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3072) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3456 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3072 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 55#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3072 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value096) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3072 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3072#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠55#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨83#u32,JGm_TX2_View.index (s00 s) indices00 values00 3072 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s00 s).«at» 3104#usize)=ok (encodeState (JGc_TX2_HashBytes.state [42,209,186,244,64,85,154,4,35,97,184,129,217,47,240,33,72,208,128,192,228,223,212,59,153,155,151,190,205,35,160,174])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 96
      5216#usize 3072#usize 3104#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings08.k1c096_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes1 0#usize 0#usize 1#usize 3104#usize 2144#usize
    55#u32 (encodeState value096) (encodeState (JGc_TX2_HashBytes.state [42,209,186,244,64,85,154,4,35,97,184,129,217,47,240,33,72,208,128,192,228,223,212,59,153,155,151,190,205,35,160,174])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read00
  simp only [show 55#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls1.source108 D hash (s00 s) 1#usize 3104#usize 55#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3104 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3072 v00
      55#u32 0#usize (encodeState value108) 3104#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 83#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 3104 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value097) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3104 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=3104#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠83#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨164#u32,JGm_TX2_View.index (s01 s) indices01 values01 3104 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s01 s).«at» 3136#usize)=ok (encodeState (JGc_TX2_HashBytes.state [82,94,77,0,170,233,221,217,248,59,144,8,3,70,235,166,198,116,219,79,252,184,193,194,47,240,55,247,228,123,125,80])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 97
      5216#usize 3104#usize 3136#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings08.k1c097_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes1 1#usize 1#usize 2#usize 3136#usize 2112#usize
    83#u32 (encodeState value097) (encodeState (JGc_TX2_HashBytes.state [82,94,77,0,170,233,221,217,248,59,144,8,3,70,235,166,198,116,219,79,252,184,193,194,47,240,55,247,228,123,125,80])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read01
  simp only [show 83#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls1.source109 D hash (s01 s) 2#usize 3136#usize 83#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 3136 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 3104 v01
      83#u32 1#usize (encodeState value109) 3136#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 164#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 3136 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value098) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3136 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=3136#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠164#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨216#u32,JGm_TX2_View.index (s02 s) indices02 values02 3136 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s02 s).«at» 3168#usize)=ok (encodeState (JGc_TX2_HashBytes.state [40,215,101,86,132,103,98,75,92,66,147,138,245,123,182,130,185,144,80,181,158,42,111,102,112,29,217,183,61,160,242,254])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 98
      5216#usize 3136#usize 3168#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings08.k1c098_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes1 2#usize 2#usize 3#usize 3168#usize 2080#usize
    164#u32 (encodeState value098) (encodeState (JGc_TX2_HashBytes.state [40,215,101,86,132,103,98,75,92,66,147,138,245,123,182,130,185,144,80,181,158,42,111,102,112,29,217,183,61,160,242,254])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read02
  simp only [show 164#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls1.source110 D hash (s02 s) 3#usize 3168#usize 164#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 3168 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 3136 v02
      164#u32 2#usize (encodeState value110) 3168#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 216#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 3168 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value099) :=
    JGm_TX2_View.value (s03 s) indices03 values03 3168 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=3168#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠216#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨249#u32,JGm_TX2_View.index (s03 s) indices03 values03 3168 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s03 s).«at» 3200#usize)=ok (encodeState (JGc_TX2_HashBytes.state [160,57,196,196,130,249,248,110,80,135,72,195,79,96,23,162,223,76,2,127,239,150,180,152,54,38,56,11,44,236,208,13])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 99
      5216#usize 3168#usize 3200#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings08.k1c099_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes1 3#usize 3#usize 4#usize 3200#usize 2048#usize
    216#u32 (encodeState value099) (encodeState (JGc_TX2_HashBytes.state [160,57,196,196,130,249,248,110,80,135,72,195,79,96,23,162,223,76,2,127,239,150,180,152,54,38,56,11,44,236,208,13])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read03
  simp only [show 216#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls1.source111 D hash (s03 s) 4#usize 3200#usize 216#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 3200 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 3168 v03
      216#u32 3#usize (encodeState value111) 3200#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 249#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 3200 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value100) :=
    JGm_TX2_View.value (s04 s) indices04 values04 3200 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=3200#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠249#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨517#u32,JGm_TX2_View.index (s04 s) indices04 values04 3200 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s04 s).«at» 3232#usize)=ok (encodeState (JGc_TX2_HashBytes.state [116,226,67,58,77,187,29,14,225,5,62,35,170,114,175,194,137,30,81,153,243,162,108,99,121,250,179,106,25,131,216,9])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 100
      5216#usize 3200#usize 3232#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings08.k1c100_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes1 4#usize 4#usize 5#usize 3232#usize 2016#usize
    249#u32 (encodeState value100) (encodeState (JGc_TX2_HashBytes.state [116,226,67,58,77,187,29,14,225,5,62,35,170,114,175,194,137,30,81,153,243,162,108,99,121,250,179,106,25,131,216,9])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read04
  simp only [show 249#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls1.source112 D hash (s04 s) 5#usize 3232#usize 249#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 3232 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 3200 v04
      249#u32 4#usize (encodeState value112) 3232#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 517#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 3232 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value101) :=
    JGm_TX2_View.value (s05 s) indices05 values05 3232 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=3232#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠517#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨584#u32,JGm_TX2_View.index (s05 s) indices05 values05 3232 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s05 s).«at» 3264#usize)=ok (encodeState (JGc_TX2_HashBytes.state [205,24,234,108,136,47,149,179,24,92,160,33,27,250,125,135,39,186,138,44,20,150,255,151,244,164,122,137,231,156,227,56])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 101
      5216#usize 3232#usize 3264#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings08.k1c101_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes1 5#usize 5#usize 6#usize 3264#usize 1984#usize
    517#u32 (encodeState value101) (encodeState (JGc_TX2_HashBytes.state [205,24,234,108,136,47,149,179,24,92,160,33,27,250,125,135,39,186,138,44,20,150,255,151,244,164,122,137,231,156,227,56])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read05
  simp only [show 517#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls1.source113 D hash (s05 s) 6#usize 3264#usize 517#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 3264 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 3232 v05
      517#u32 5#usize (encodeState value113) 3264#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 584#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 3264 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value102) :=
    JGm_TX2_View.value (s06 s) indices06 values06 3264 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=3264#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠584#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨649#u32,JGm_TX2_View.index (s06 s) indices06 values06 3264 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s06 s).«at» 3296#usize)=ok (encodeState (JGc_TX2_HashBytes.state [39,12,46,158,191,34,15,221,80,208,28,205,102,142,235,84,148,88,40,247,140,63,129,255,161,161,15,77,142,197,121,39])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 102
      5216#usize 3264#usize 3296#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings08.k1c102_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes1 6#usize 6#usize 7#usize 3296#usize 1952#usize
    584#u32 (encodeState value102) (encodeState (JGc_TX2_HashBytes.state [39,12,46,158,191,34,15,221,80,208,28,205,102,142,235,84,148,88,40,247,140,63,129,255,161,161,15,77,142,197,121,39])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read06
  simp only [show 584#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls1.source114 D hash (s06 s) 7#usize 3296#usize 584#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 3296 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 3264 v06
      584#u32 6#usize (encodeState value114) 3296#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 649#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 3296 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value103) :=
    JGm_TX2_View.value (s07 s) indices07 values07 3296 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=3296#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠649#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨695#u32,JGm_TX2_View.index (s07 s) indices07 values07 3296 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s07 s).«at» 3328#usize)=ok (encodeState (JGc_TX2_HashBytes.state [38,238,25,53,205,238,129,18,16,93,50,14,32,86,40,21,253,116,219,94,108,165,120,233,186,94,13,166,208,144,221,232])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 103
      5216#usize 3296#usize 3328#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings08.k1c103_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes1 7#usize 7#usize 8#usize 3328#usize 1920#usize
    649#u32 (encodeState value103) (encodeState (JGc_TX2_HashBytes.state [38,238,25,53,205,238,129,18,16,93,50,14,32,86,40,21,253,116,219,94,108,165,120,233,186,94,13,166,208,144,221,232])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read07
  simp only [show 649#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls1.source115 D hash (s07 s) 8#usize 3328#usize 649#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 3328 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 3296 v07
      649#u32 7#usize (encodeState value115) 3328#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 695#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 3328 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value104) :=
    JGm_TX2_View.value (s08 s) indices08 values08 3328 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=3328#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠695#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨701#u32,JGm_TX2_View.index (s08 s) indices08 values08 3328 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s08 s).«at» 3360#usize)=ok (encodeState (JGc_TX2_HashBytes.state [127,62,114,156,149,104,203,143,198,183,255,114,201,117,117,82,111,158,99,45,121,239,255,80,117,205,134,73,3,69,196,155])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 104
      5216#usize 3328#usize 3360#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings08.k1c104_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes1 8#usize 8#usize 9#usize 3360#usize 1888#usize
    695#u32 (encodeState value104) (encodeState (JGc_TX2_HashBytes.state [127,62,114,156,149,104,203,143,198,183,255,114,201,117,117,82,111,158,99,45,121,239,255,80,117,205,134,73,3,69,196,155])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read08
  simp only [show 695#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls1.source116 D hash (s08 s) 9#usize 3360#usize 695#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 3360 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 3328 v08
      695#u32 8#usize (encodeState value116) 3360#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 701#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 3360 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value105) :=
    JGm_TX2_View.value (s09 s) indices09 values09 3360 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=3360#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠701#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨725#u32,JGm_TX2_View.index (s09 s) indices09 values09 3360 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s09 s).«at» 3392#usize)=ok (encodeState (JGc_TX2_HashBytes.state [224,37,184,12,191,94,24,26,69,182,112,205,185,74,122,3,77,167,47,60,187,191,139,12,139,18,24,163,135,242,85,237])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 105
      5216#usize 3360#usize 3392#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings08.k1c105_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes1 9#usize 9#usize 10#usize 3392#usize 1856#usize
    701#u32 (encodeState value105) (encodeState (JGc_TX2_HashBytes.state [224,37,184,12,191,94,24,26,69,182,112,205,185,74,122,3,77,167,47,60,187,191,139,12,139,18,24,163,135,242,85,237])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read09
  simp only [show 701#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls1.source117 D hash (s09 s) 10#usize 3392#usize 701#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 3392 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 3360 v09
      701#u32 9#usize (encodeState value117) 3392#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 725#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 3392 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value106) :=
    JGm_TX2_View.value (s10 s) indices10 values10 3392 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=3392#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠725#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨851#u32,JGm_TX2_View.index (s10 s) indices10 values10 3392 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s10 s).«at» 3424#usize)=ok (encodeState (JGc_TX2_HashBytes.state [16,187,227,107,21,139,209,135,146,50,74,200,68,177,53,46,81,235,223,80,24,55,150,247,82,241,210,90,155,135,139,189])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 106
      5216#usize 3392#usize 3424#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings08.k1c106_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes1 10#usize 10#usize 11#usize 3424#usize 1824#usize
    725#u32 (encodeState value106) (encodeState (JGc_TX2_HashBytes.state [16,187,227,107,21,139,209,135,146,50,74,200,68,177,53,46,81,235,223,80,24,55,150,247,82,241,210,90,155,135,139,189])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read10
  simp only [show 725#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes1 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls1.source118 D hash (s10 s) 11#usize 3424#usize 725#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 3424 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 3392 v10
      725#u32 10#usize (encodeState value118) 3424#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 851#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 3424 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value107) :=
    JGm_TX2_View.value (s11 s) indices11 values11 3424 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=3424#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠851#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s11 s).«at» 3456#usize)=ok (encodeState (JGc_TX2_HashBytes.state [45,226,164,129,82,202,216,10,56,42,239,25,88,158,122,240,236,117,68,125,2,101,195,154,23,85,105,223,50,236,125,117])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 107
      5216#usize 3424#usize 3456#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings08.k1c107_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes1 11#usize 11#usize 12#usize 3456#usize 1792#usize
    851#u32 (encodeState value107) (encodeState (JGc_TX2_HashBytes.state [45,226,164,129,82,202,216,10,56,42,239,25,88,158,122,240,236,117,68,125,2,101,195,154,23,85,105,223,50,236,125,117])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read11
  simp only [show 851#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes1 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls1.source119 D hash (s11 s) 12#usize 3456#usize 851#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 3456 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 3424 v11
      851#u32 11#usize (encodeState value119) 3456#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 3456
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level1_08
end
