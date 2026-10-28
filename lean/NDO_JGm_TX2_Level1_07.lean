import NDO_JGm_TX2_ParentCalls1
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level1_07
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGh_TX2_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes1
def indices00 : List U32 := [111#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,1403#u32,1450#u32,1703#u32]
def values00 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 111#u32 0#usize (encodeState value096) 2720#usize
 def indices01 : List U32 := [55#u32,166#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,1403#u32,1450#u32,1703#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value096,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 166#u32 1#usize (encodeState value097) 2752#usize
 def indices02 : List U32 := [55#u32,83#u32,329#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,1403#u32,1450#u32,1703#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value096,encodeState value097,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 329#u32 2#usize (encodeState value098) 2784#usize
 def indices03 : List U32 := [55#u32,83#u32,164#u32,432#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,1403#u32,1450#u32,1703#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value096,encodeState value097,encodeState value098,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 432#u32 3#usize (encodeState value099) 2816#usize
 def indices04 : List U32 := [55#u32,83#u32,164#u32,216#u32,498#u32,1034#u32,1168#u32,1298#u32,1391#u32,1403#u32,1450#u32,1703#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value096,encodeState value097,encodeState value098,encodeState value099,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 498#u32 4#usize (encodeState value100) 2848#usize
 def indices05 : List U32 := [55#u32,83#u32,164#u32,216#u32,249#u32,1034#u32,1168#u32,1298#u32,1391#u32,1403#u32,1450#u32,1703#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value096,encodeState value097,encodeState value098,encodeState value099,encodeState value100,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 1034#u32 5#usize (encodeState value101) 2880#usize
 def indices06 : List U32 := [55#u32,83#u32,164#u32,216#u32,249#u32,517#u32,1168#u32,1298#u32,1391#u32,1403#u32,1450#u32,1703#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value096,encodeState value097,encodeState value098,encodeState value099,encodeState value100,encodeState value101,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 1168#u32 6#usize (encodeState value102) 2912#usize
 def indices07 : List U32 := [55#u32,83#u32,164#u32,216#u32,249#u32,517#u32,584#u32,1298#u32,1391#u32,1403#u32,1450#u32,1703#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value096,encodeState value097,encodeState value098,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 1298#u32 7#usize (encodeState value103) 2944#usize
 def indices08 : List U32 := [55#u32,83#u32,164#u32,216#u32,249#u32,517#u32,584#u32,649#u32,1391#u32,1403#u32,1450#u32,1703#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value096,encodeState value097,encodeState value098,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value092,encodeState value093,encodeState value094,encodeState value095]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 1391#u32 8#usize (encodeState value104) 2976#usize
 def indices09 : List U32 := [55#u32,83#u32,164#u32,216#u32,249#u32,517#u32,584#u32,649#u32,695#u32,1403#u32,1450#u32,1703#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value096,encodeState value097,encodeState value098,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value093,encodeState value094,encodeState value095]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 1403#u32 9#usize (encodeState value105) 3008#usize
 def indices10 : List U32 := [55#u32,83#u32,164#u32,216#u32,249#u32,517#u32,584#u32,649#u32,695#u32,701#u32,1450#u32,1703#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value096,encodeState value097,encodeState value098,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value094,encodeState value095]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 1450#u32 10#usize (encodeState value106) 3040#usize
 def indices11 : List U32 := [55#u32,83#u32,164#u32,216#u32,249#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,1703#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value096,encodeState value097,encodeState value098,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value095]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 1703#u32 11#usize (encodeState value107) 3072#usize
 def indices12 : List U32 := [55#u32,83#u32,164#u32,216#u32,249#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value096,encodeState value097,encodeState value098,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [55#u32,83#u32,164#u32,216#u32,249#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value096,encodeState value097,encodeState value098,encodeState value099,encodeState value100,encodeState value101,encodeState value102,encodeState value103,encodeState value104,encodeState value105,encodeState value106,encodeState value107]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 2688) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3072 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 2688 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 111#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 2688 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value084) :=
    JGm_TX2_View.value (s00 s) indices00 values00 2688 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=2688#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠111#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨166#u32,JGm_TX2_View.index (s00 s) indices00 values00 2688 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s00 s).«at» 2720#usize)=ok (encodeState (JGc_TX2_HashBytes.state [203,9,133,227,15,195,21,115,223,53,152,174,124,199,4,94,229,118,63,214,217,122,22,128,174,253,10,14,171,97,252,197])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 84
      5216#usize 2688#usize 2720#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings07.k1c084_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes1 0#usize 0#usize 1#usize 2720#usize 2528#usize
    111#u32 (encodeState value084) (encodeState (JGc_TX2_HashBytes.state [203,9,133,227,15,195,21,115,223,53,152,174,124,199,4,94,229,118,63,214,217,122,22,128,174,253,10,14,171,97,252,197])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read00
  simp only [show 111#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls1.source096 D hash (s00 s) 1#usize 2720#usize 111#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 2720 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 2688 v00
      111#u32 0#usize (encodeState value096) 2720#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 166#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 2720 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value085) :=
    JGm_TX2_View.value (s01 s) indices01 values01 2720 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=2720#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠166#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨329#u32,JGm_TX2_View.index (s01 s) indices01 values01 2720 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s01 s).«at» 2752#usize)=ok (encodeState (JGc_TX2_HashBytes.state [4,111,221,72,213,154,98,139,231,197,10,227,180,103,86,61,114,160,110,73,66,39,22,40,71,225,154,223,55,58,205,108])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 85
      5216#usize 2720#usize 2752#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings07.k1c085_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes1 1#usize 1#usize 2#usize 2752#usize 2496#usize
    166#u32 (encodeState value085) (encodeState (JGc_TX2_HashBytes.state [4,111,221,72,213,154,98,139,231,197,10,227,180,103,86,61,114,160,110,73,66,39,22,40,71,225,154,223,55,58,205,108])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read01
  simp only [show 166#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls1.source097 D hash (s01 s) 2#usize 2752#usize 166#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 2752 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 2720 v01
      166#u32 1#usize (encodeState value097) 2752#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 329#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 2752 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value086) :=
    JGm_TX2_View.value (s02 s) indices02 values02 2752 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=2752#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠329#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨432#u32,JGm_TX2_View.index (s02 s) indices02 values02 2752 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s02 s).«at» 2784#usize)=ok (encodeState (JGc_TX2_HashBytes.state [73,249,200,133,96,173,28,175,204,110,144,41,6,64,159,174,225,179,179,207,101,205,137,114,231,100,35,81,143,125,160,80])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 86
      5216#usize 2752#usize 2784#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings07.k1c086_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes1 2#usize 2#usize 3#usize 2784#usize 2464#usize
    329#u32 (encodeState value086) (encodeState (JGc_TX2_HashBytes.state [73,249,200,133,96,173,28,175,204,110,144,41,6,64,159,174,225,179,179,207,101,205,137,114,231,100,35,81,143,125,160,80])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read02
  simp only [show 329#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls1.source098 D hash (s02 s) 3#usize 2784#usize 329#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 2784 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 2752 v02
      329#u32 2#usize (encodeState value098) 2784#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 432#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 2784 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value087) :=
    JGm_TX2_View.value (s03 s) indices03 values03 2784 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=2784#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠432#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨498#u32,JGm_TX2_View.index (s03 s) indices03 values03 2784 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s03 s).«at» 2816#usize)=ok (encodeState (JGc_TX2_HashBytes.state [40,152,225,228,234,20,139,186,209,211,179,52,223,219,213,227,61,184,135,134,121,131,254,163,17,154,210,129,147,10,15,237])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 87
      5216#usize 2784#usize 2816#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings07.k1c087_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes1 3#usize 3#usize 4#usize 2816#usize 2432#usize
    432#u32 (encodeState value087) (encodeState (JGc_TX2_HashBytes.state [40,152,225,228,234,20,139,186,209,211,179,52,223,219,213,227,61,184,135,134,121,131,254,163,17,154,210,129,147,10,15,237])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read03
  simp only [show 432#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls1.source099 D hash (s03 s) 4#usize 2816#usize 432#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 2816 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 2784 v03
      432#u32 3#usize (encodeState value099) 2816#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 498#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 2816 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value088) :=
    JGm_TX2_View.value (s04 s) indices04 values04 2816 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=2816#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠498#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1034#u32,JGm_TX2_View.index (s04 s) indices04 values04 2816 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s04 s).«at» 2848#usize)=ok (encodeState (JGc_TX2_HashBytes.state [240,142,169,184,183,101,200,198,128,106,126,146,216,97,129,238,198,129,196,235,159,83,117,254,163,93,137,7,144,104,234,135])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 88
      5216#usize 2816#usize 2848#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings07.k1c088_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes1 4#usize 4#usize 5#usize 2848#usize 2400#usize
    498#u32 (encodeState value088) (encodeState (JGc_TX2_HashBytes.state [240,142,169,184,183,101,200,198,128,106,126,146,216,97,129,238,198,129,196,235,159,83,117,254,163,93,137,7,144,104,234,135])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read04
  simp only [show 498#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls1.source100 D hash (s04 s) 5#usize 2848#usize 498#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 2848 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 2816 v04
      498#u32 4#usize (encodeState value100) 2848#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 1034#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 2848 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value089) :=
    JGm_TX2_View.value (s05 s) indices05 values05 2848 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=2848#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠1034#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1168#u32,JGm_TX2_View.index (s05 s) indices05 values05 2848 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s05 s).«at» 2880#usize)=ok (encodeState (JGc_TX2_HashBytes.state [194,210,7,150,249,28,210,137,57,196,112,39,213,114,31,103,65,61,98,96,111,4,214,212,17,250,158,230,132,1,25,147])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 89
      5216#usize 2848#usize 2880#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings07.k1c089_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes1 5#usize 5#usize 6#usize 2880#usize 2368#usize
    1034#u32 (encodeState value089) (encodeState (JGc_TX2_HashBytes.state [194,210,7,150,249,28,210,137,57,196,112,39,213,114,31,103,65,61,98,96,111,4,214,212,17,250,158,230,132,1,25,147])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read05
  simp only [show 1034#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls1.source101 D hash (s05 s) 6#usize 2880#usize 1034#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 2880 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 2848 v05
      1034#u32 5#usize (encodeState value101) 2880#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 1168#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 2880 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value090) :=
    JGm_TX2_View.value (s06 s) indices06 values06 2880 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=2880#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠1168#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1298#u32,JGm_TX2_View.index (s06 s) indices06 values06 2880 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s06 s).«at» 2912#usize)=ok (encodeState (JGc_TX2_HashBytes.state [239,30,19,252,85,32,149,121,101,222,131,47,177,239,199,64,148,207,250,56,169,32,232,115,191,143,189,147,209,21,196,209])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 90
      5216#usize 2880#usize 2912#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings07.k1c090_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes1 6#usize 6#usize 7#usize 2912#usize 2336#usize
    1168#u32 (encodeState value090) (encodeState (JGc_TX2_HashBytes.state [239,30,19,252,85,32,149,121,101,222,131,47,177,239,199,64,148,207,250,56,169,32,232,115,191,143,189,147,209,21,196,209])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read06
  simp only [show 1168#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls1.source102 D hash (s06 s) 7#usize 2912#usize 1168#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 2912 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 2880 v06
      1168#u32 6#usize (encodeState value102) 2912#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 1298#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 2912 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value091) :=
    JGm_TX2_View.value (s07 s) indices07 values07 2912 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=2912#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠1298#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1391#u32,JGm_TX2_View.index (s07 s) indices07 values07 2912 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s07 s).«at» 2944#usize)=ok (encodeState (JGc_TX2_HashBytes.state [143,95,171,144,248,1,113,242,91,50,229,44,34,64,188,191,101,120,169,118,86,155,27,164,177,185,137,226,233,96,216,49])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 91
      5216#usize 2912#usize 2944#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings07.k1c091_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes1 7#usize 7#usize 8#usize 2944#usize 2304#usize
    1298#u32 (encodeState value091) (encodeState (JGc_TX2_HashBytes.state [143,95,171,144,248,1,113,242,91,50,229,44,34,64,188,191,101,120,169,118,86,155,27,164,177,185,137,226,233,96,216,49])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read07
  simp only [show 1298#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls1.source103 D hash (s07 s) 8#usize 2944#usize 1298#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 2944 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 2912 v07
      1298#u32 7#usize (encodeState value103) 2944#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 1391#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 2944 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value092) :=
    JGm_TX2_View.value (s08 s) indices08 values08 2944 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=2944#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠1391#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1403#u32,JGm_TX2_View.index (s08 s) indices08 values08 2944 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s08 s).«at» 2976#usize)=ok (encodeState (JGc_TX2_HashBytes.state [120,184,180,182,8,74,113,147,122,226,22,124,100,32,230,17,155,26,169,107,143,50,96,36,14,170,84,170,213,28,126,106])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 92
      5216#usize 2944#usize 2976#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings07.k1c092_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes1 8#usize 8#usize 9#usize 2976#usize 2272#usize
    1391#u32 (encodeState value092) (encodeState (JGc_TX2_HashBytes.state [120,184,180,182,8,74,113,147,122,226,22,124,100,32,230,17,155,26,169,107,143,50,96,36,14,170,84,170,213,28,126,106])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read08
  simp only [show 1391#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls1.source104 D hash (s08 s) 9#usize 2976#usize 1391#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 2976 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 2944 v08
      1391#u32 8#usize (encodeState value104) 2976#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 1403#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 2976 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value093) :=
    JGm_TX2_View.value (s09 s) indices09 values09 2976 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=2976#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠1403#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1450#u32,JGm_TX2_View.index (s09 s) indices09 values09 2976 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s09 s).«at» 3008#usize)=ok (encodeState (JGc_TX2_HashBytes.state [217,0,49,133,129,84,241,85,163,17,81,91,191,20,0,243,27,242,234,67,185,82,199,214,175,143,194,28,186,243,133,44])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 93
      5216#usize 2976#usize 3008#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings07.k1c093_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes1 9#usize 9#usize 10#usize 3008#usize 2240#usize
    1403#u32 (encodeState value093) (encodeState (JGc_TX2_HashBytes.state [217,0,49,133,129,84,241,85,163,17,81,91,191,20,0,243,27,242,234,67,185,82,199,214,175,143,194,28,186,243,133,44])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read09
  simp only [show 1403#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls1.source105 D hash (s09 s) 10#usize 3008#usize 1403#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 3008 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 2976 v09
      1403#u32 9#usize (encodeState value105) 3008#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 1450#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 3008 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value094) :=
    JGm_TX2_View.value (s10 s) indices10 values10 3008 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=3008#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠1450#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨1703#u32,JGm_TX2_View.index (s10 s) indices10 values10 3008 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s10 s).«at» 3040#usize)=ok (encodeState (JGc_TX2_HashBytes.state [174,76,24,53,14,201,201,53,29,168,105,97,99,242,26,158,165,206,196,172,222,174,132,172,223,235,1,115,185,246,112,40])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 94
      5216#usize 3008#usize 3040#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings07.k1c094_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes1 10#usize 10#usize 11#usize 3040#usize 2208#usize
    1450#u32 (encodeState value094) (encodeState (JGc_TX2_HashBytes.state [174,76,24,53,14,201,201,53,29,168,105,97,99,242,26,158,165,206,196,172,222,174,132,172,223,235,1,115,185,246,112,40])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read10
  simp only [show 1450#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes1 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls1.source106 D hash (s10 s) 11#usize 3040#usize 1450#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 3040 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 3008 v10
      1450#u32 10#usize (encodeState value106) 3040#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 1703#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 3040 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value095) :=
    JGm_TX2_View.value (s11 s) indices11 values11 3040 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=3040#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠1703#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s11 s).«at» 3072#usize)=ok (encodeState (JGc_TX2_HashBytes.state [254,149,11,180,204,235,24,36,233,34,55,139,83,230,33,23,28,105,193,218,39,103,170,119,89,206,184,198,95,29,57,222])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 95
      5216#usize 3040#usize 3072#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings07.k1c095_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes1 11#usize 11#usize 12#usize 3072#usize 2176#usize
    1703#u32 (encodeState value095) (encodeState (JGc_TX2_HashBytes.state [254,149,11,180,204,235,24,36,233,34,55,139,83,230,33,23,28,105,193,218,39,103,170,119,89,206,184,198,95,29,57,222])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read11
  simp only [show 1703#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes1 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls1.source107 D hash (s11 s) 12#usize 3072#usize 1703#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 3072 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 3040 v11
      1703#u32 11#usize (encodeState value107) 3072#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 3072
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level1_07
end
