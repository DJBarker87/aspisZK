import NDO_JGm_TX2_ParentCalls0
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level0_08
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGf_TX2_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes0
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
      s JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
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
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s00 s).«at» 3104#usize)=ok (encodeState (JGc_TX2_HashBytes.state [2,46,34,254,218,4,158,107,130,46,114,8,60,95,94,87,229,185,115,156,99,154,199,78,59,36,238,72,42,151,211,188])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 96
      5216#usize 3072#usize 3104#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings08.k0c096_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes0 0#usize 0#usize 1#usize 3104#usize 2144#usize
    55#u32 (encodeState value096) (encodeState (JGc_TX2_HashBytes.state [2,46,34,254,218,4,158,107,130,46,114,8,60,95,94,87,229,185,115,156,99,154,199,78,59,36,238,72,42,151,211,188])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read00
  simp only [show 55#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls0.source108 D hash (s00 s) 1#usize 3104#usize 55#u32 0#usize (by decide)
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
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s01 s).«at» 3136#usize)=ok (encodeState (JGc_TX2_HashBytes.state [154,208,77,161,184,67,183,200,214,218,136,37,98,103,67,103,151,155,56,146,131,95,186,128,119,190,122,199,199,52,253,226])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 97
      5216#usize 3104#usize 3136#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings08.k0c097_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes0 1#usize 1#usize 2#usize 3136#usize 2112#usize
    83#u32 (encodeState value097) (encodeState (JGc_TX2_HashBytes.state [154,208,77,161,184,67,183,200,214,218,136,37,98,103,67,103,151,155,56,146,131,95,186,128,119,190,122,199,199,52,253,226])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read01
  simp only [show 83#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes0 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls0.source109 D hash (s01 s) 2#usize 3136#usize 83#u32 1#usize (by decide)
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
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s02 s).«at» 3168#usize)=ok (encodeState (JGc_TX2_HashBytes.state [176,111,170,43,1,17,170,220,146,210,5,234,213,229,223,243,68,212,160,189,189,189,180,163,254,22,150,205,181,134,121,150])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 98
      5216#usize 3136#usize 3168#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings08.k0c098_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes0 2#usize 2#usize 3#usize 3168#usize 2080#usize
    164#u32 (encodeState value098) (encodeState (JGc_TX2_HashBytes.state [176,111,170,43,1,17,170,220,146,210,5,234,213,229,223,243,68,212,160,189,189,189,180,163,254,22,150,205,181,134,121,150])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read02
  simp only [show 164#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes0 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls0.source110 D hash (s02 s) 3#usize 3168#usize 164#u32 2#usize (by decide)
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
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s03 s).«at» 3200#usize)=ok (encodeState (JGc_TX2_HashBytes.state [190,30,19,138,221,217,158,23,123,111,209,117,218,71,70,238,212,87,112,130,100,166,107,207,132,180,152,66,132,181,25,230])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 99
      5216#usize 3168#usize 3200#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings08.k0c099_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes0 3#usize 3#usize 4#usize 3200#usize 2048#usize
    216#u32 (encodeState value099) (encodeState (JGc_TX2_HashBytes.state [190,30,19,138,221,217,158,23,123,111,209,117,218,71,70,238,212,87,112,130,100,166,107,207,132,180,152,66,132,181,25,230])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read03
  simp only [show 216#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes0 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls0.source111 D hash (s03 s) 4#usize 3200#usize 216#u32 3#usize (by decide)
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
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s04 s).«at» 3232#usize)=ok (encodeState (JGc_TX2_HashBytes.state [133,166,92,247,178,14,164,71,151,110,197,203,112,216,136,220,103,44,2,220,22,22,191,100,50,245,93,176,39,78,244,152])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 100
      5216#usize 3200#usize 3232#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings08.k0c100_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes0 4#usize 4#usize 5#usize 3232#usize 2016#usize
    249#u32 (encodeState value100) (encodeState (JGc_TX2_HashBytes.state [133,166,92,247,178,14,164,71,151,110,197,203,112,216,136,220,103,44,2,220,22,22,191,100,50,245,93,176,39,78,244,152])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read04
  simp only [show 249#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes0 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls0.source112 D hash (s04 s) 5#usize 3232#usize 249#u32 4#usize (by decide)
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
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s05 s).«at» 3264#usize)=ok (encodeState (JGc_TX2_HashBytes.state [66,185,148,49,55,63,224,95,221,106,45,169,131,64,148,207,5,79,16,110,85,52,26,163,173,177,45,89,111,30,47,204])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 101
      5216#usize 3232#usize 3264#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings08.k0c101_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes0 5#usize 5#usize 6#usize 3264#usize 1984#usize
    517#u32 (encodeState value101) (encodeState (JGc_TX2_HashBytes.state [66,185,148,49,55,63,224,95,221,106,45,169,131,64,148,207,5,79,16,110,85,52,26,163,173,177,45,89,111,30,47,204])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read05
  simp only [show 517#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes0 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls0.source113 D hash (s05 s) 6#usize 3264#usize 517#u32 5#usize (by decide)
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
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s06 s).«at» 3296#usize)=ok (encodeState (JGc_TX2_HashBytes.state [203,231,182,96,201,188,17,123,246,219,105,254,212,38,128,220,25,18,216,70,109,209,62,47,85,82,139,104,54,108,26,95])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 102
      5216#usize 3264#usize 3296#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings08.k0c102_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes0 6#usize 6#usize 7#usize 3296#usize 1952#usize
    584#u32 (encodeState value102) (encodeState (JGc_TX2_HashBytes.state [203,231,182,96,201,188,17,123,246,219,105,254,212,38,128,220,25,18,216,70,109,209,62,47,85,82,139,104,54,108,26,95])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read06
  simp only [show 584#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes0 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls0.source114 D hash (s06 s) 7#usize 3296#usize 584#u32 6#usize (by decide)
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
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s07 s).«at» 3328#usize)=ok (encodeState (JGc_TX2_HashBytes.state [8,10,154,102,135,84,59,156,16,207,44,29,73,106,208,210,219,249,52,74,89,130,162,71,30,71,209,194,230,192,207,219])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 103
      5216#usize 3296#usize 3328#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings08.k0c103_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes0 7#usize 7#usize 8#usize 3328#usize 1920#usize
    649#u32 (encodeState value103) (encodeState (JGc_TX2_HashBytes.state [8,10,154,102,135,84,59,156,16,207,44,29,73,106,208,210,219,249,52,74,89,130,162,71,30,71,209,194,230,192,207,219])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read07
  simp only [show 649#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes0 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls0.source115 D hash (s07 s) 8#usize 3328#usize 649#u32 7#usize (by decide)
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
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s08 s).«at» 3360#usize)=ok (encodeState (JGc_TX2_HashBytes.state [240,111,122,80,145,91,112,149,1,108,228,205,17,59,20,157,121,182,38,17,182,149,228,59,217,0,133,119,93,88,71,12])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 104
      5216#usize 3328#usize 3360#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings08.k0c104_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes0 8#usize 8#usize 9#usize 3360#usize 1888#usize
    695#u32 (encodeState value104) (encodeState (JGc_TX2_HashBytes.state [240,111,122,80,145,91,112,149,1,108,228,205,17,59,20,157,121,182,38,17,182,149,228,59,217,0,133,119,93,88,71,12])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read08
  simp only [show 695#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes0 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls0.source116 D hash (s08 s) 9#usize 3360#usize 695#u32 8#usize (by decide)
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
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s09 s).«at» 3392#usize)=ok (encodeState (JGc_TX2_HashBytes.state [72,253,183,126,163,29,80,199,72,132,128,240,147,13,169,213,238,49,18,180,38,79,65,52,42,202,78,86,137,131,199,24])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 105
      5216#usize 3360#usize 3392#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings08.k0c105_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes0 9#usize 9#usize 10#usize 3392#usize 1856#usize
    701#u32 (encodeState value105) (encodeState (JGc_TX2_HashBytes.state [72,253,183,126,163,29,80,199,72,132,128,240,147,13,169,213,238,49,18,180,38,79,65,52,42,202,78,86,137,131,199,24])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read09
  simp only [show 701#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes0 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls0.source117 D hash (s09 s) 10#usize 3392#usize 701#u32 9#usize (by decide)
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
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s10 s).«at» 3424#usize)=ok (encodeState (JGc_TX2_HashBytes.state [33,112,127,42,228,224,95,157,136,181,107,4,15,173,123,113,22,13,51,115,167,196,208,116,229,137,5,14,34,253,89,94])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 106
      5216#usize 3392#usize 3424#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings08.k0c106_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes0 10#usize 10#usize 11#usize 3424#usize 1824#usize
    725#u32 (encodeState value106) (encodeState (JGc_TX2_HashBytes.state [33,112,127,42,228,224,95,157,136,181,107,4,15,173,123,113,22,13,51,115,167,196,208,116,229,137,5,14,34,253,89,94])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read10
  simp only [show 725#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes0 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls0.source118 D hash (s10 s) 11#usize 3424#usize 725#u32 10#usize (by decide)
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
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s11 s).«at» 3456#usize)=ok (encodeState (JGc_TX2_HashBytes.state [27,158,254,158,67,152,206,7,93,54,237,102,39,250,48,129,45,41,54,54,255,249,55,104,159,3,85,132,188,88,238,69])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 107
      5216#usize 3424#usize 3456#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings08.k0c107_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes0 11#usize 11#usize 12#usize 3456#usize 1792#usize
    851#u32 (encodeState value107) (encodeState (JGc_TX2_HashBytes.state [27,158,254,158,67,152,206,7,93,54,237,102,39,250,48,129,45,41,54,54,255,249,55,104,159,3,85,132,188,88,238,69])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read11
  simp only [show 851#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes0 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls0.source119 D hash (s11 s) 12#usize 3456#usize 851#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 3456 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 3424 v11
      851#u32 11#usize (encodeState value119) 3456#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 3456
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level0_08
end
