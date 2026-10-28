import NDO_JGm_TX2_ParentCalls0
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level0_10
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGf_TX2_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes0
def indices00 : List U32 := [13#u32,20#u32,41#u32,54#u32,62#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
def values00 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130,encodeState value131]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 13#u32 0#usize (encodeState value132) 3872#usize
 def indices01 : List U32 := [6#u32,20#u32,41#u32,54#u32,62#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value132,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130,encodeState value131]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 20#u32 1#usize (encodeState value133) 3904#usize
 def indices02 : List U32 := [6#u32,10#u32,41#u32,54#u32,62#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value132,encodeState value133,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130,encodeState value131]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 41#u32 2#usize (encodeState value134) 3936#usize
 def indices03 : List U32 := [6#u32,10#u32,20#u32,54#u32,62#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value132,encodeState value133,encodeState value134,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130,encodeState value131]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 54#u32 3#usize (encodeState value135) 3968#usize
 def indices04 : List U32 := [6#u32,10#u32,20#u32,27#u32,62#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130,encodeState value131]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 62#u32 4#usize (encodeState value136) 4000#usize
 def indices05 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,129#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130,encodeState value131]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 129#u32 5#usize (encodeState value137) 4032#usize
 def indices06 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,146#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130,encodeState value131]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 146#u32 6#usize (encodeState value138) 4064#usize
 def indices07 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,162#u32,173#u32,175#u32,181#u32,212#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value127,encodeState value128,encodeState value129,encodeState value130,encodeState value131]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 162#u32 7#usize (encodeState value139) 4096#usize
 def indices08 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,173#u32,175#u32,181#u32,212#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value128,encodeState value129,encodeState value130,encodeState value131]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 173#u32 8#usize (encodeState value140) 4128#usize
 def indices09 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,175#u32,181#u32,212#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value140,encodeState value129,encodeState value130,encodeState value131]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 175#u32 9#usize (encodeState value141) 4160#usize
 def indices10 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,181#u32,212#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value140,encodeState value141,encodeState value130,encodeState value131]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 181#u32 10#usize (encodeState value142) 4192#usize
 def indices11 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,212#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value131]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 212#u32 11#usize (encodeState value143) 4224#usize
 def indices12 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3840) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 4224 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3840 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 13#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3840 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value120) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3840 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3840#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠13#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨20#u32,JGm_TX2_View.index (s00 s) indices00 values00 3840 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s00 s).«at» 3872#usize)=ok (encodeState (JGc_TX2_HashBytes.state [72,180,73,182,98,64,191,234,128,146,240,255,73,14,27,166,200,56,147,223,196,200,249,249,189,122,13,171,27,214,43,203])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 120
      5216#usize 3840#usize 3872#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings10.k0c120_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes0 0#usize 0#usize 1#usize 3872#usize 1376#usize
    13#u32 (encodeState value120) (encodeState (JGc_TX2_HashBytes.state [72,180,73,182,98,64,191,234,128,146,240,255,73,14,27,166,200,56,147,223,196,200,249,249,189,122,13,171,27,214,43,203])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read00
  simp only [show 13#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls0.source132 D hash (s00 s) 1#usize 3872#usize 13#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3872 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3840 v00
      13#u32 0#usize (encodeState value132) 3872#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 20#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 3872 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value121) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3872 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=3872#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠20#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨41#u32,JGm_TX2_View.index (s01 s) indices01 values01 3872 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s01 s).«at» 3904#usize)=ok (encodeState (JGc_TX2_HashBytes.state [99,55,47,196,216,220,150,214,26,215,49,37,196,159,43,69,134,69,125,176,189,7,116,111,19,162,247,218,179,95,57,101])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 121
      5216#usize 3872#usize 3904#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings10.k0c121_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes0 1#usize 1#usize 2#usize 3904#usize 1344#usize
    20#u32 (encodeState value121) (encodeState (JGc_TX2_HashBytes.state [99,55,47,196,216,220,150,214,26,215,49,37,196,159,43,69,134,69,125,176,189,7,116,111,19,162,247,218,179,95,57,101])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read01
  simp only [show 20#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes0 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls0.source133 D hash (s01 s) 2#usize 3904#usize 20#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 3904 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 3872 v01
      20#u32 1#usize (encodeState value133) 3904#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 41#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 3904 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value122) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3904 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=3904#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠41#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨54#u32,JGm_TX2_View.index (s02 s) indices02 values02 3904 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s02 s).«at» 3936#usize)=ok (encodeState (JGc_TX2_HashBytes.state [48,35,138,61,209,36,109,184,163,56,38,182,136,104,9,198,1,40,217,79,189,78,236,56,74,180,157,230,46,56,48,127])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 122
      5216#usize 3904#usize 3936#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings10.k0c122_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes0 2#usize 2#usize 3#usize 3936#usize 1312#usize
    41#u32 (encodeState value122) (encodeState (JGc_TX2_HashBytes.state [48,35,138,61,209,36,109,184,163,56,38,182,136,104,9,198,1,40,217,79,189,78,236,56,74,180,157,230,46,56,48,127])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read02
  simp only [show 41#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes0 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls0.source134 D hash (s02 s) 3#usize 3936#usize 41#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 3936 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 3904 v02
      41#u32 2#usize (encodeState value134) 3936#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 54#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 3936 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value123) :=
    JGm_TX2_View.value (s03 s) indices03 values03 3936 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=3936#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠54#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨62#u32,JGm_TX2_View.index (s03 s) indices03 values03 3936 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s03 s).«at» 3968#usize)=ok (encodeState (JGc_TX2_HashBytes.state [184,223,76,18,255,19,236,254,70,250,44,16,118,252,48,207,204,62,99,98,225,145,168,186,25,132,2,159,114,128,37,127])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 123
      5216#usize 3936#usize 3968#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings10.k0c123_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes0 3#usize 3#usize 4#usize 3968#usize 1280#usize
    54#u32 (encodeState value123) (encodeState (JGc_TX2_HashBytes.state [184,223,76,18,255,19,236,254,70,250,44,16,118,252,48,207,204,62,99,98,225,145,168,186,25,132,2,159,114,128,37,127])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read03
  simp only [show 54#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes0 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls0.source135 D hash (s03 s) 4#usize 3968#usize 54#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 3968 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 3936 v03
      54#u32 3#usize (encodeState value135) 3968#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 62#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 3968 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value124) :=
    JGm_TX2_View.value (s04 s) indices04 values04 3968 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=3968#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠62#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨129#u32,JGm_TX2_View.index (s04 s) indices04 values04 3968 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s04 s).«at» 4000#usize)=ok (encodeState (JGc_TX2_HashBytes.state [66,141,179,78,169,251,218,97,201,26,66,226,78,26,2,34,37,59,246,203,179,179,241,151,182,171,135,192,49,236,167,185])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 124
      5216#usize 3968#usize 4000#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings10.k0c124_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes0 4#usize 4#usize 5#usize 4000#usize 1248#usize
    62#u32 (encodeState value124) (encodeState (JGc_TX2_HashBytes.state [66,141,179,78,169,251,218,97,201,26,66,226,78,26,2,34,37,59,246,203,179,179,241,151,182,171,135,192,49,236,167,185])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read04
  simp only [show 62#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes0 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls0.source136 D hash (s04 s) 5#usize 4000#usize 62#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 4000 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 3968 v04
      62#u32 4#usize (encodeState value136) 4000#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 129#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 4000 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value125) :=
    JGm_TX2_View.value (s05 s) indices05 values05 4000 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=4000#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠129#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨146#u32,JGm_TX2_View.index (s05 s) indices05 values05 4000 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s05 s).«at» 4032#usize)=ok (encodeState (JGc_TX2_HashBytes.state [41,177,207,57,62,0,184,61,82,15,215,73,118,152,135,82,134,32,219,151,133,84,187,130,80,72,107,237,131,208,37,192])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 125
      5216#usize 4000#usize 4032#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings10.k0c125_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes0 5#usize 5#usize 6#usize 4032#usize 1216#usize
    129#u32 (encodeState value125) (encodeState (JGc_TX2_HashBytes.state [41,177,207,57,62,0,184,61,82,15,215,73,118,152,135,82,134,32,219,151,133,84,187,130,80,72,107,237,131,208,37,192])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read05
  simp only [show 129#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes0 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls0.source137 D hash (s05 s) 6#usize 4032#usize 129#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 4032 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 4000 v05
      129#u32 5#usize (encodeState value137) 4032#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 146#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 4032 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value126) :=
    JGm_TX2_View.value (s06 s) indices06 values06 4032 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=4032#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠146#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨162#u32,JGm_TX2_View.index (s06 s) indices06 values06 4032 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s06 s).«at» 4064#usize)=ok (encodeState (JGc_TX2_HashBytes.state [232,58,255,55,61,162,16,23,237,138,180,89,16,0,29,233,199,125,198,23,154,183,15,126,29,226,80,163,57,60,144,18])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 126
      5216#usize 4032#usize 4064#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings10.k0c126_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes0 6#usize 6#usize 7#usize 4064#usize 1184#usize
    146#u32 (encodeState value126) (encodeState (JGc_TX2_HashBytes.state [232,58,255,55,61,162,16,23,237,138,180,89,16,0,29,233,199,125,198,23,154,183,15,126,29,226,80,163,57,60,144,18])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read06
  simp only [show 146#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes0 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls0.source138 D hash (s06 s) 7#usize 4064#usize 146#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 4064 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 4032 v06
      146#u32 6#usize (encodeState value138) 4064#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 162#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 4064 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value127) :=
    JGm_TX2_View.value (s07 s) indices07 values07 4064 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=4064#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠162#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨173#u32,JGm_TX2_View.index (s07 s) indices07 values07 4064 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s07 s).«at» 4096#usize)=ok (encodeState (JGc_TX2_HashBytes.state [66,135,130,77,225,162,97,219,9,212,25,0,174,230,39,177,29,144,180,21,29,206,227,123,53,59,149,186,161,243,86,37])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 127
      5216#usize 4064#usize 4096#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings10.k0c127_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes0 7#usize 7#usize 8#usize 4096#usize 1152#usize
    162#u32 (encodeState value127) (encodeState (JGc_TX2_HashBytes.state [66,135,130,77,225,162,97,219,9,212,25,0,174,230,39,177,29,144,180,21,29,206,227,123,53,59,149,186,161,243,86,37])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read07
  simp only [show 162#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes0 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls0.source139 D hash (s07 s) 8#usize 4096#usize 162#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 4096 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 4064 v07
      162#u32 7#usize (encodeState value139) 4096#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 173#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 4096 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value128) :=
    JGm_TX2_View.value (s08 s) indices08 values08 4096 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=4096#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠173#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨175#u32,JGm_TX2_View.index (s08 s) indices08 values08 4096 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s08 s).«at» 4128#usize)=ok (encodeState (JGc_TX2_HashBytes.state [87,231,15,129,229,140,140,137,141,83,142,209,172,213,234,174,242,147,38,64,211,180,251,125,80,101,85,191,4,119,233,205])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 128
      5216#usize 4096#usize 4128#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings10.k0c128_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes0 8#usize 8#usize 9#usize 4128#usize 1120#usize
    173#u32 (encodeState value128) (encodeState (JGc_TX2_HashBytes.state [87,231,15,129,229,140,140,137,141,83,142,209,172,213,234,174,242,147,38,64,211,180,251,125,80,101,85,191,4,119,233,205])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read08
  simp only [show 173#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes0 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls0.source140 D hash (s08 s) 9#usize 4128#usize 173#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 4128 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 4096 v08
      173#u32 8#usize (encodeState value140) 4128#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 175#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 4128 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value129) :=
    JGm_TX2_View.value (s09 s) indices09 values09 4128 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=4128#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠175#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨181#u32,JGm_TX2_View.index (s09 s) indices09 values09 4128 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s09 s).«at» 4160#usize)=ok (encodeState (JGc_TX2_HashBytes.state [46,88,184,203,19,143,21,236,210,222,11,211,12,28,213,15,25,253,11,68,231,193,149,194,181,144,125,71,175,74,186,244])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 129
      5216#usize 4128#usize 4160#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings10.k0c129_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes0 9#usize 9#usize 10#usize 4160#usize 1088#usize
    175#u32 (encodeState value129) (encodeState (JGc_TX2_HashBytes.state [46,88,184,203,19,143,21,236,210,222,11,211,12,28,213,15,25,253,11,68,231,193,149,194,181,144,125,71,175,74,186,244])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read09
  simp only [show 175#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes0 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls0.source141 D hash (s09 s) 10#usize 4160#usize 175#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 4160 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 4128 v09
      175#u32 9#usize (encodeState value141) 4160#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 181#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 4160 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value130) :=
    JGm_TX2_View.value (s10 s) indices10 values10 4160 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=4160#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠181#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨212#u32,JGm_TX2_View.index (s10 s) indices10 values10 4160 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s10 s).«at» 4192#usize)=ok (encodeState (JGc_TX2_HashBytes.state [219,159,99,156,149,23,192,251,78,146,99,40,200,112,21,200,102,96,128,83,23,240,114,66,84,178,247,49,16,64,10,17])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 130
      5216#usize 4160#usize 4192#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings10.k0c130_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes0 10#usize 10#usize 11#usize 4192#usize 1056#usize
    181#u32 (encodeState value130) (encodeState (JGc_TX2_HashBytes.state [219,159,99,156,149,23,192,251,78,146,99,40,200,112,21,200,102,96,128,83,23,240,114,66,84,178,247,49,16,64,10,17])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read10
  simp only [show 181#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes0 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls0.source142 D hash (s10 s) 11#usize 4192#usize 181#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 4192 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 4160 v10
      181#u32 10#usize (encodeState value142) 4192#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 212#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 4192 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value131) :=
    JGm_TX2_View.value (s11 s) indices11 values11 4192 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=4192#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠212#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s11 s).«at» 4224#usize)=ok (encodeState (JGc_TX2_HashBytes.state [90,100,221,216,88,163,24,57,180,29,244,239,26,122,234,171,251,20,109,18,152,138,5,195,6,172,202,58,41,146,6,210])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 131
      5216#usize 4192#usize 4224#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings10.k0c131_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes0 11#usize 11#usize 12#usize 4224#usize 1024#usize
    212#u32 (encodeState value131) (encodeState (JGc_TX2_HashBytes.state [90,100,221,216,88,163,24,57,180,29,244,239,26,122,234,171,251,20,109,18,152,138,5,195,6,172,202,58,41,146,6,210])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read11
  simp only [show 212#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes0 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls0.source143 D hash (s11 s) 12#usize 4224#usize 212#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 4224 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 4192 v11
      212#u32 11#usize (encodeState value143) 4224#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 4224
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level0_10
end
