import NDO_JGm_TX2_ParentCalls2
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level2_06
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGc_TX2_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes2
def indices00 : List U32 := [55#u32,83#u32,164#u32,216#u32,249#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
def values00 : List (Array U8 32#usize) := [encodeState value072,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 55#u32 0#usize (encodeState value084) 2336#usize
 def indices01 : List U32 := [27#u32,83#u32,164#u32,216#u32,249#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value084,encodeState value073,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 83#u32 1#usize (encodeState value085) 2368#usize
 def indices02 : List U32 := [27#u32,41#u32,164#u32,216#u32,249#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value074,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 164#u32 2#usize (encodeState value086) 2400#usize
 def indices03 : List U32 := [27#u32,41#u32,82#u32,216#u32,249#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value075,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 216#u32 3#usize (encodeState value087) 2432#usize
 def indices04 : List U32 := [27#u32,41#u32,82#u32,108#u32,249#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value076,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 249#u32 4#usize (encodeState value088) 2464#usize
 def indices05 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,517#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value077,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 517#u32 5#usize (encodeState value089) 2496#usize
 def indices06 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,584#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value078,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 584#u32 6#usize (encodeState value090) 2528#usize
 def indices07 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,649#u32,695#u32,701#u32,725#u32,851#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value079,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 649#u32 7#usize (encodeState value091) 2560#usize
 def indices08 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,695#u32,701#u32,725#u32,851#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value080,encodeState value081,encodeState value082,encodeState value083]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 695#u32 8#usize (encodeState value092) 2592#usize
 def indices09 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,347#u32,701#u32,725#u32,851#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value081,encodeState value082,encodeState value083]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 701#u32 9#usize (encodeState value093) 2624#usize
 def indices10 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,347#u32,350#u32,725#u32,851#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value082,encodeState value083]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 725#u32 10#usize (encodeState value094) 2656#usize
 def indices11 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,347#u32,350#u32,362#u32,851#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value083]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 851#u32 11#usize (encodeState value095) 2688#usize
 def indices12 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,347#u32,350#u32,362#u32,425#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,347#u32,350#u32,362#u32,425#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value084,encodeState value085,encodeState value086,encodeState value087,encodeState value088,encodeState value089,encodeState value090,encodeState value091,encodeState value092,encodeState value093,encodeState value094,encodeState value095]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 2304) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 2688 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 2304 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 55#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 2304 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value072) :=
    JGm_TX2_View.value (s00 s) indices00 values00 2304 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=2304#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠55#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨83#u32,JGm_TX2_View.index (s00 s) indices00 values00 2304 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s00 s).«at» 2336#usize)=ok (encodeState (JGc_TX2_HashBytes.state [172,67,137,129,63,172,213,184,246,140,203,189,136,215,89,220,185,230,208,158,18,177,217,98,222,72,135,93,172,40,32,160])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 72
      4512#usize 2304#usize 2336#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings06.k2c072_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes2 0#usize 0#usize 1#usize 2336#usize 2208#usize
    55#u32 (encodeState value072) (encodeState (JGc_TX2_HashBytes.state [172,67,137,129,63,172,213,184,246,140,203,189,136,215,89,220,185,230,208,158,18,177,217,98,222,72,135,93,172,40,32,160])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read00
  simp only [show 55#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls2.source084 D hash (s00 s) 1#usize 2336#usize 55#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 2336 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 2304 v00
      55#u32 0#usize (encodeState value084) 2336#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 83#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 2336 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value073) :=
    JGm_TX2_View.value (s01 s) indices01 values01 2336 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=2336#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠83#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨164#u32,JGm_TX2_View.index (s01 s) indices01 values01 2336 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s01 s).«at» 2368#usize)=ok (encodeState (JGc_TX2_HashBytes.state [192,100,6,122,185,90,6,201,115,33,239,251,7,29,119,219,203,29,219,48,33,203,239,165,153,210,29,187,213,92,243,99])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 73
      4512#usize 2336#usize 2368#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings06.k2c073_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes2 1#usize 1#usize 2#usize 2368#usize 2176#usize
    83#u32 (encodeState value073) (encodeState (JGc_TX2_HashBytes.state [192,100,6,122,185,90,6,201,115,33,239,251,7,29,119,219,203,29,219,48,33,203,239,165,153,210,29,187,213,92,243,99])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read01
  simp only [show 83#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls2.source085 D hash (s01 s) 2#usize 2368#usize 83#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 2368 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 2336 v01
      83#u32 1#usize (encodeState value085) 2368#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 164#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 2368 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value074) :=
    JGm_TX2_View.value (s02 s) indices02 values02 2368 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=2368#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠164#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨216#u32,JGm_TX2_View.index (s02 s) indices02 values02 2368 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s02 s).«at» 2400#usize)=ok (encodeState (JGc_TX2_HashBytes.state [160,29,86,39,155,246,138,139,59,225,193,197,98,181,170,87,251,47,4,91,110,122,32,141,127,177,72,246,75,220,36,248])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 74
      4512#usize 2368#usize 2400#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings06.k2c074_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes2 2#usize 2#usize 3#usize 2400#usize 2144#usize
    164#u32 (encodeState value074) (encodeState (JGc_TX2_HashBytes.state [160,29,86,39,155,246,138,139,59,225,193,197,98,181,170,87,251,47,4,91,110,122,32,141,127,177,72,246,75,220,36,248])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read02
  simp only [show 164#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls2.source086 D hash (s02 s) 3#usize 2400#usize 164#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 2400 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 2368 v02
      164#u32 2#usize (encodeState value086) 2400#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 216#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 2400 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value075) :=
    JGm_TX2_View.value (s03 s) indices03 values03 2400 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=2400#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠216#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨249#u32,JGm_TX2_View.index (s03 s) indices03 values03 2400 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s03 s).«at» 2432#usize)=ok (encodeState (JGc_TX2_HashBytes.state [166,214,63,214,11,10,238,8,114,208,36,118,8,70,86,233,111,73,40,88,18,215,83,213,47,162,199,7,118,175,34,210])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 75
      4512#usize 2400#usize 2432#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings06.k2c075_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes2 3#usize 3#usize 4#usize 2432#usize 2112#usize
    216#u32 (encodeState value075) (encodeState (JGc_TX2_HashBytes.state [166,214,63,214,11,10,238,8,114,208,36,118,8,70,86,233,111,73,40,88,18,215,83,213,47,162,199,7,118,175,34,210])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read03
  simp only [show 216#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes2 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls2.source087 D hash (s03 s) 4#usize 2432#usize 216#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 2432 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 2400 v03
      216#u32 3#usize (encodeState value087) 2432#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 249#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 2432 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value076) :=
    JGm_TX2_View.value (s04 s) indices04 values04 2432 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=2432#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠249#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨517#u32,JGm_TX2_View.index (s04 s) indices04 values04 2432 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s04 s).«at» 2464#usize)=ok (encodeState (JGc_TX2_HashBytes.state [30,61,92,235,182,187,57,4,63,191,154,138,172,134,38,222,106,62,228,28,131,136,27,9,126,38,80,228,211,133,248,231])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 76
      4512#usize 2432#usize 2464#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings06.k2c076_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes2 4#usize 4#usize 5#usize 2464#usize 2080#usize
    249#u32 (encodeState value076) (encodeState (JGc_TX2_HashBytes.state [30,61,92,235,182,187,57,4,63,191,154,138,172,134,38,222,106,62,228,28,131,136,27,9,126,38,80,228,211,133,248,231])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read04
  simp only [show 249#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes2 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls2.source088 D hash (s04 s) 5#usize 2464#usize 249#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 2464 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 2432 v04
      249#u32 4#usize (encodeState value088) 2464#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 517#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 2464 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value077) :=
    JGm_TX2_View.value (s05 s) indices05 values05 2464 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=2464#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠517#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨584#u32,JGm_TX2_View.index (s05 s) indices05 values05 2464 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s05 s).«at» 2496#usize)=ok (encodeState (JGc_TX2_HashBytes.state [223,165,248,99,102,245,66,219,179,246,44,60,203,239,166,162,96,176,21,241,209,235,211,87,48,252,109,199,219,229,103,200])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 77
      4512#usize 2464#usize 2496#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings06.k2c077_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes2 5#usize 5#usize 6#usize 2496#usize 2048#usize
    517#u32 (encodeState value077) (encodeState (JGc_TX2_HashBytes.state [223,165,248,99,102,245,66,219,179,246,44,60,203,239,166,162,96,176,21,241,209,235,211,87,48,252,109,199,219,229,103,200])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read05
  simp only [show 517#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes2 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls2.source089 D hash (s05 s) 6#usize 2496#usize 517#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 2496 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 2464 v05
      517#u32 5#usize (encodeState value089) 2496#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 584#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 2496 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value078) :=
    JGm_TX2_View.value (s06 s) indices06 values06 2496 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=2496#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠584#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨649#u32,JGm_TX2_View.index (s06 s) indices06 values06 2496 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s06 s).«at» 2528#usize)=ok (encodeState (JGc_TX2_HashBytes.state [198,62,134,252,113,214,123,111,76,28,128,123,190,175,101,40,132,7,35,191,80,154,161,188,17,46,52,203,135,65,166,112])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 78
      4512#usize 2496#usize 2528#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings06.k2c078_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes2 6#usize 6#usize 7#usize 2528#usize 2016#usize
    584#u32 (encodeState value078) (encodeState (JGc_TX2_HashBytes.state [198,62,134,252,113,214,123,111,76,28,128,123,190,175,101,40,132,7,35,191,80,154,161,188,17,46,52,203,135,65,166,112])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read06
  simp only [show 584#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes2 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls2.source090 D hash (s06 s) 7#usize 2528#usize 584#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 2528 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 2496 v06
      584#u32 6#usize (encodeState value090) 2528#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 649#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 2528 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value079) :=
    JGm_TX2_View.value (s07 s) indices07 values07 2528 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=2528#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠649#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨695#u32,JGm_TX2_View.index (s07 s) indices07 values07 2528 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s07 s).«at» 2560#usize)=ok (encodeState (JGc_TX2_HashBytes.state [36,197,178,9,230,13,104,143,163,9,16,179,99,249,195,81,219,27,81,56,198,108,12,53,89,178,43,172,163,62,170,112])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 79
      4512#usize 2528#usize 2560#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings06.k2c079_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes2 7#usize 7#usize 8#usize 2560#usize 1984#usize
    649#u32 (encodeState value079) (encodeState (JGc_TX2_HashBytes.state [36,197,178,9,230,13,104,143,163,9,16,179,99,249,195,81,219,27,81,56,198,108,12,53,89,178,43,172,163,62,170,112])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read07
  simp only [show 649#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes2 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls2.source091 D hash (s07 s) 8#usize 2560#usize 649#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 2560 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 2528 v07
      649#u32 7#usize (encodeState value091) 2560#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 695#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 2560 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value080) :=
    JGm_TX2_View.value (s08 s) indices08 values08 2560 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=2560#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠695#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨701#u32,JGm_TX2_View.index (s08 s) indices08 values08 2560 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s08 s).«at» 2592#usize)=ok (encodeState (JGc_TX2_HashBytes.state [22,236,166,67,21,215,141,209,71,132,132,197,43,37,138,88,199,164,115,143,69,63,202,239,219,4,159,98,48,77,237,83])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 80
      4512#usize 2560#usize 2592#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings06.k2c080_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes2 8#usize 8#usize 9#usize 2592#usize 1952#usize
    695#u32 (encodeState value080) (encodeState (JGc_TX2_HashBytes.state [22,236,166,67,21,215,141,209,71,132,132,197,43,37,138,88,199,164,115,143,69,63,202,239,219,4,159,98,48,77,237,83])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read08
  simp only [show 695#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes2 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls2.source092 D hash (s08 s) 9#usize 2592#usize 695#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 2592 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 2560 v08
      695#u32 8#usize (encodeState value092) 2592#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 701#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 2592 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value081) :=
    JGm_TX2_View.value (s09 s) indices09 values09 2592 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=2592#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠701#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨725#u32,JGm_TX2_View.index (s09 s) indices09 values09 2592 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s09 s).«at» 2624#usize)=ok (encodeState (JGc_TX2_HashBytes.state [182,212,215,63,255,39,69,5,133,254,2,40,136,4,209,190,155,88,38,45,233,136,227,145,61,147,86,118,142,35,104,75])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 81
      4512#usize 2592#usize 2624#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings06.k2c081_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes2 9#usize 9#usize 10#usize 2624#usize 1920#usize
    701#u32 (encodeState value081) (encodeState (JGc_TX2_HashBytes.state [182,212,215,63,255,39,69,5,133,254,2,40,136,4,209,190,155,88,38,45,233,136,227,145,61,147,86,118,142,35,104,75])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read09
  simp only [show 701#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes2 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls2.source093 D hash (s09 s) 10#usize 2624#usize 701#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 2624 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 2592 v09
      701#u32 9#usize (encodeState value093) 2624#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 725#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 2624 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value082) :=
    JGm_TX2_View.value (s10 s) indices10 values10 2624 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=2624#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠725#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨851#u32,JGm_TX2_View.index (s10 s) indices10 values10 2624 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s10 s).«at» 2656#usize)=ok (encodeState (JGc_TX2_HashBytes.state [221,190,144,37,250,148,161,205,45,236,191,55,74,22,137,113,22,102,151,155,29,24,36,48,178,187,189,138,113,62,215,119])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 82
      4512#usize 2624#usize 2656#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings06.k2c082_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes2 10#usize 10#usize 11#usize 2656#usize 1888#usize
    725#u32 (encodeState value082) (encodeState (JGc_TX2_HashBytes.state [221,190,144,37,250,148,161,205,45,236,191,55,74,22,137,113,22,102,151,155,29,24,36,48,178,187,189,138,113,62,215,119])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read10
  simp only [show 725#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes2 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls2.source094 D hash (s10 s) 11#usize 2656#usize 725#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 2656 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 2624 v10
      725#u32 10#usize (encodeState value094) 2656#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 851#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 2656 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value083) :=
    JGm_TX2_View.value (s11 s) indices11 values11 2656 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=2656#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠851#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s11 s).«at» 2688#usize)=ok (encodeState (JGc_TX2_HashBytes.state [159,122,129,237,10,27,151,100,235,23,81,3,119,58,53,120,161,156,210,101,211,167,134,168,116,89,18,3,55,73,7,207])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 83
      4512#usize 2656#usize 2688#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings06.k2c083_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes2 11#usize 11#usize 12#usize 2688#usize 1856#usize
    851#u32 (encodeState value083) (encodeState (JGc_TX2_HashBytes.state [159,122,129,237,10,27,151,100,235,23,81,3,119,58,53,120,161,156,210,101,211,167,134,168,116,89,18,3,55,73,7,207])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read11
  simp only [show 851#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes2 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls2.source095 D hash (s11 s) 12#usize 2688#usize 851#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 2688 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 2656 v11
      851#u32 11#usize (encodeState value095) 2688#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 2688
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level2_06
end
