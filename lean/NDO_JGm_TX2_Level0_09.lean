import NDO_JGm_TX2_ParentCalls0
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level0_09
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGf_TX2_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes0
def indices00 : List U32 := [27#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,347#u32,350#u32,362#u32,425#u32]
def values00 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 27#u32 0#usize (encodeState value120) 3488#usize
 def indices01 : List U32 := [13#u32,41#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,347#u32,350#u32,362#u32,425#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value120,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 41#u32 1#usize (encodeState value121) 3520#usize
 def indices02 : List U32 := [13#u32,20#u32,82#u32,108#u32,124#u32,258#u32,292#u32,324#u32,347#u32,350#u32,362#u32,425#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 82#u32 2#usize (encodeState value122) 3552#usize
 def indices03 : List U32 := [13#u32,20#u32,41#u32,108#u32,124#u32,258#u32,292#u32,324#u32,347#u32,350#u32,362#u32,425#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 108#u32 3#usize (encodeState value123) 3584#usize
 def indices04 : List U32 := [13#u32,20#u32,41#u32,54#u32,124#u32,258#u32,292#u32,324#u32,347#u32,350#u32,362#u32,425#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 124#u32 4#usize (encodeState value124) 3616#usize
 def indices05 : List U32 := [13#u32,20#u32,41#u32,54#u32,62#u32,258#u32,292#u32,324#u32,347#u32,350#u32,362#u32,425#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 258#u32 5#usize (encodeState value125) 3648#usize
 def indices06 : List U32 := [13#u32,20#u32,41#u32,54#u32,62#u32,129#u32,292#u32,324#u32,347#u32,350#u32,362#u32,425#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 292#u32 6#usize (encodeState value126) 3680#usize
 def indices07 : List U32 := [13#u32,20#u32,41#u32,54#u32,62#u32,129#u32,146#u32,324#u32,347#u32,350#u32,362#u32,425#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 324#u32 7#usize (encodeState value127) 3712#usize
 def indices08 : List U32 := [13#u32,20#u32,41#u32,54#u32,62#u32,129#u32,146#u32,162#u32,347#u32,350#u32,362#u32,425#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 347#u32 8#usize (encodeState value128) 3744#usize
 def indices09 : List U32 := [13#u32,20#u32,41#u32,54#u32,62#u32,129#u32,146#u32,162#u32,173#u32,350#u32,362#u32,425#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value117,encodeState value118,encodeState value119]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 350#u32 9#usize (encodeState value129) 3776#usize
 def indices10 : List U32 := [13#u32,20#u32,41#u32,54#u32,62#u32,129#u32,146#u32,162#u32,173#u32,175#u32,362#u32,425#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value118,encodeState value119]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 362#u32 10#usize (encodeState value130) 3808#usize
 def indices11 : List U32 := [13#u32,20#u32,41#u32,54#u32,62#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,425#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130,encodeState value119]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 425#u32 11#usize (encodeState value131) 3840#usize
 def indices12 : List U32 := [13#u32,20#u32,41#u32,54#u32,62#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130,encodeState value131]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [13#u32,20#u32,41#u32,54#u32,62#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130,encodeState value131]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3456) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3840 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3456 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 27#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3456 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value108) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3456 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3456#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠27#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨41#u32,JGm_TX2_View.index (s00 s) indices00 values00 3456 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s00 s).«at» 3488#usize)=ok (encodeState (JGc_TX2_HashBytes.state [137,254,59,77,179,1,237,247,200,120,110,235,77,151,11,244,92,96,109,81,19,103,169,240,252,130,236,210,163,132,192,218])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 108
      5216#usize 3456#usize 3488#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings09.k0c108_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes0 0#usize 0#usize 1#usize 3488#usize 1760#usize
    27#u32 (encodeState value108) (encodeState (JGc_TX2_HashBytes.state [137,254,59,77,179,1,237,247,200,120,110,235,77,151,11,244,92,96,109,81,19,103,169,240,252,130,236,210,163,132,192,218])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read00
  simp only [show 27#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls0.source120 D hash (s00 s) 1#usize 3488#usize 27#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3488 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3456 v00
      27#u32 0#usize (encodeState value120) 3488#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 41#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 3488 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value109) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3488 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=3488#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠41#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨82#u32,JGm_TX2_View.index (s01 s) indices01 values01 3488 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s01 s).«at» 3520#usize)=ok (encodeState (JGc_TX2_HashBytes.state [134,221,191,174,186,191,252,123,193,134,138,82,87,172,163,2,237,117,79,223,223,251,208,53,139,246,171,236,233,6,77,3])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 109
      5216#usize 3488#usize 3520#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings09.k0c109_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes0 1#usize 1#usize 2#usize 3520#usize 1728#usize
    41#u32 (encodeState value109) (encodeState (JGc_TX2_HashBytes.state [134,221,191,174,186,191,252,123,193,134,138,82,87,172,163,2,237,117,79,223,223,251,208,53,139,246,171,236,233,6,77,3])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read01
  simp only [show 41#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes0 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls0.source121 D hash (s01 s) 2#usize 3520#usize 41#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 3520 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 3488 v01
      41#u32 1#usize (encodeState value121) 3520#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 82#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 3520 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value110) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3520 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=3520#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠82#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨108#u32,JGm_TX2_View.index (s02 s) indices02 values02 3520 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s02 s).«at» 3552#usize)=ok (encodeState (JGc_TX2_HashBytes.state [158,188,166,145,252,238,128,108,69,125,61,32,225,11,18,243,109,180,72,125,53,29,240,243,77,13,232,8,87,39,196,54])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 110
      5216#usize 3520#usize 3552#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings09.k0c110_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes0 2#usize 2#usize 3#usize 3552#usize 1696#usize
    82#u32 (encodeState value110) (encodeState (JGc_TX2_HashBytes.state [158,188,166,145,252,238,128,108,69,125,61,32,225,11,18,243,109,180,72,125,53,29,240,243,77,13,232,8,87,39,196,54])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read02
  simp only [show 82#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes0 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls0.source122 D hash (s02 s) 3#usize 3552#usize 82#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 3552 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 3520 v02
      82#u32 2#usize (encodeState value122) 3552#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 108#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 3552 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value111) :=
    JGm_TX2_View.value (s03 s) indices03 values03 3552 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=3552#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠108#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨124#u32,JGm_TX2_View.index (s03 s) indices03 values03 3552 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s03 s).«at» 3584#usize)=ok (encodeState (JGc_TX2_HashBytes.state [134,183,217,160,61,62,118,106,201,58,81,129,242,85,11,16,232,8,48,194,235,5,153,13,197,48,222,29,216,220,118,218])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 111
      5216#usize 3552#usize 3584#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings09.k0c111_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes0 3#usize 3#usize 4#usize 3584#usize 1664#usize
    108#u32 (encodeState value111) (encodeState (JGc_TX2_HashBytes.state [134,183,217,160,61,62,118,106,201,58,81,129,242,85,11,16,232,8,48,194,235,5,153,13,197,48,222,29,216,220,118,218])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read03
  simp only [show 108#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes0 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls0.source123 D hash (s03 s) 4#usize 3584#usize 108#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 3584 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 3552 v03
      108#u32 3#usize (encodeState value123) 3584#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 124#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 3584 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value112) :=
    JGm_TX2_View.value (s04 s) indices04 values04 3584 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=3584#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠124#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨258#u32,JGm_TX2_View.index (s04 s) indices04 values04 3584 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s04 s).«at» 3616#usize)=ok (encodeState (JGc_TX2_HashBytes.state [194,75,62,73,149,126,92,216,3,31,137,160,0,179,111,17,82,59,203,25,134,92,135,36,53,107,196,137,67,118,76,207])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 112
      5216#usize 3584#usize 3616#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings09.k0c112_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes0 4#usize 4#usize 5#usize 3616#usize 1632#usize
    124#u32 (encodeState value112) (encodeState (JGc_TX2_HashBytes.state [194,75,62,73,149,126,92,216,3,31,137,160,0,179,111,17,82,59,203,25,134,92,135,36,53,107,196,137,67,118,76,207])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read04
  simp only [show 124#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes0 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls0.source124 D hash (s04 s) 5#usize 3616#usize 124#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 3616 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 3584 v04
      124#u32 4#usize (encodeState value124) 3616#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 258#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 3616 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value113) :=
    JGm_TX2_View.value (s05 s) indices05 values05 3616 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=3616#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠258#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨292#u32,JGm_TX2_View.index (s05 s) indices05 values05 3616 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s05 s).«at» 3648#usize)=ok (encodeState (JGc_TX2_HashBytes.state [232,33,236,201,71,140,177,43,225,119,15,140,193,231,0,109,11,184,7,193,153,182,83,143,225,104,53,248,251,8,186,225])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 113
      5216#usize 3616#usize 3648#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings09.k0c113_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes0 5#usize 5#usize 6#usize 3648#usize 1600#usize
    258#u32 (encodeState value113) (encodeState (JGc_TX2_HashBytes.state [232,33,236,201,71,140,177,43,225,119,15,140,193,231,0,109,11,184,7,193,153,182,83,143,225,104,53,248,251,8,186,225])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read05
  simp only [show 258#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes0 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls0.source125 D hash (s05 s) 6#usize 3648#usize 258#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 3648 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 3616 v05
      258#u32 5#usize (encodeState value125) 3648#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 292#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 3648 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value114) :=
    JGm_TX2_View.value (s06 s) indices06 values06 3648 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=3648#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠292#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨324#u32,JGm_TX2_View.index (s06 s) indices06 values06 3648 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s06 s).«at» 3680#usize)=ok (encodeState (JGc_TX2_HashBytes.state [154,107,206,221,148,212,50,234,184,152,97,83,125,197,210,252,0,144,121,59,175,92,17,41,109,90,234,49,242,126,30,214])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 114
      5216#usize 3648#usize 3680#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings09.k0c114_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes0 6#usize 6#usize 7#usize 3680#usize 1568#usize
    292#u32 (encodeState value114) (encodeState (JGc_TX2_HashBytes.state [154,107,206,221,148,212,50,234,184,152,97,83,125,197,210,252,0,144,121,59,175,92,17,41,109,90,234,49,242,126,30,214])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read06
  simp only [show 292#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes0 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls0.source126 D hash (s06 s) 7#usize 3680#usize 292#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 3680 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 3648 v06
      292#u32 6#usize (encodeState value126) 3680#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 324#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 3680 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value115) :=
    JGm_TX2_View.value (s07 s) indices07 values07 3680 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=3680#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠324#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨347#u32,JGm_TX2_View.index (s07 s) indices07 values07 3680 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s07 s).«at» 3712#usize)=ok (encodeState (JGc_TX2_HashBytes.state [212,94,32,221,151,187,112,240,12,6,105,149,114,164,22,116,123,228,245,126,133,199,85,85,151,255,86,229,174,21,251,16])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 115
      5216#usize 3680#usize 3712#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings09.k0c115_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes0 7#usize 7#usize 8#usize 3712#usize 1536#usize
    324#u32 (encodeState value115) (encodeState (JGc_TX2_HashBytes.state [212,94,32,221,151,187,112,240,12,6,105,149,114,164,22,116,123,228,245,126,133,199,85,85,151,255,86,229,174,21,251,16])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read07
  simp only [show 324#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes0 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls0.source127 D hash (s07 s) 8#usize 3712#usize 324#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 3712 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 3680 v07
      324#u32 7#usize (encodeState value127) 3712#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 347#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 3712 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value116) :=
    JGm_TX2_View.value (s08 s) indices08 values08 3712 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=3712#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠347#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨350#u32,JGm_TX2_View.index (s08 s) indices08 values08 3712 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s08 s).«at» 3744#usize)=ok (encodeState (JGc_TX2_HashBytes.state [62,243,108,186,159,33,162,85,98,168,211,189,49,231,79,84,22,43,165,170,76,205,173,176,109,116,232,236,11,77,196,218])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 116
      5216#usize 3712#usize 3744#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings09.k0c116_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes0 8#usize 8#usize 9#usize 3744#usize 1504#usize
    347#u32 (encodeState value116) (encodeState (JGc_TX2_HashBytes.state [62,243,108,186,159,33,162,85,98,168,211,189,49,231,79,84,22,43,165,170,76,205,173,176,109,116,232,236,11,77,196,218])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read08
  simp only [show 347#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes0 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls0.source128 D hash (s08 s) 9#usize 3744#usize 347#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 3744 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 3712 v08
      347#u32 8#usize (encodeState value128) 3744#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 350#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 3744 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value117) :=
    JGm_TX2_View.value (s09 s) indices09 values09 3744 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=3744#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠350#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨362#u32,JGm_TX2_View.index (s09 s) indices09 values09 3744 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s09 s).«at» 3776#usize)=ok (encodeState (JGc_TX2_HashBytes.state [80,210,160,246,253,173,51,247,62,105,138,203,245,24,184,58,160,58,94,60,3,17,9,138,50,204,50,80,178,140,222,205])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 117
      5216#usize 3744#usize 3776#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings09.k0c117_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes0 9#usize 9#usize 10#usize 3776#usize 1472#usize
    350#u32 (encodeState value117) (encodeState (JGc_TX2_HashBytes.state [80,210,160,246,253,173,51,247,62,105,138,203,245,24,184,58,160,58,94,60,3,17,9,138,50,204,50,80,178,140,222,205])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read09
  simp only [show 350#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes0 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls0.source129 D hash (s09 s) 10#usize 3776#usize 350#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 3776 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 3744 v09
      350#u32 9#usize (encodeState value129) 3776#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 362#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 3776 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value118) :=
    JGm_TX2_View.value (s10 s) indices10 values10 3776 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=3776#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠362#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨425#u32,JGm_TX2_View.index (s10 s) indices10 values10 3776 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s10 s).«at» 3808#usize)=ok (encodeState (JGc_TX2_HashBytes.state [221,212,44,181,141,94,253,153,10,170,182,151,70,225,201,125,188,174,56,204,24,120,91,96,254,67,179,157,151,35,254,73])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 118
      5216#usize 3776#usize 3808#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings09.k0c118_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes0 10#usize 10#usize 11#usize 3808#usize 1440#usize
    362#u32 (encodeState value118) (encodeState (JGc_TX2_HashBytes.state [221,212,44,181,141,94,253,153,10,170,182,151,70,225,201,125,188,174,56,204,24,120,91,96,254,67,179,157,151,35,254,73])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read10
  simp only [show 362#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes0 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls0.source130 D hash (s10 s) 11#usize 3808#usize 362#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 3808 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 3776 v10
      362#u32 10#usize (encodeState value130) 3808#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 425#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 3808 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value119) :=
    JGm_TX2_View.value (s11 s) indices11 values11 3808 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=3808#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠425#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s11 s).«at» 3840#usize)=ok (encodeState (JGc_TX2_HashBytes.state [200,62,212,180,142,24,117,229,188,84,170,85,119,151,238,93,230,127,174,104,53,125,47,231,123,1,4,236,68,152,147,74])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 119
      5216#usize 3808#usize 3840#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings09.k0c119_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes0 11#usize 11#usize 12#usize 3840#usize 1408#usize
    425#u32 (encodeState value119) (encodeState (JGc_TX2_HashBytes.state [200,62,212,180,142,24,117,229,188,84,170,85,119,151,238,93,230,127,174,104,53,125,47,231,123,1,4,236,68,152,147,74])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read11
  simp only [show 425#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes0 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls0.source131 D hash (s11 s) 12#usize 3840#usize 425#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 3840 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 3808 v11
      425#u32 11#usize (encodeState value131) 3840#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 3840
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level0_09
end
