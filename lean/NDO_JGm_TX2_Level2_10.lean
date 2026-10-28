import NDO_JGm_TX2_ParentCalls2
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level2_10
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGc_TX2_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes2
def indices00 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
def values00 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 3#u32 0#usize (encodeState value131) 3808#usize
 def indices01 : List U32 := [1#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value131,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 5#u32 1#usize (encodeState value132) 3840#usize
 def indices02 : List U32 := [1#u32,2#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 10#u32 2#usize (encodeState value133) 3872#usize
 def indices03 : List U32 := [1#u32,2#u32,5#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value133,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 13#u32 3#usize (encodeState value134) 3904#usize
 def indices04 : List U32 := [1#u32,2#u32,5#u32,6#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 15#u32 4#usize (encodeState value135) 3936#usize
 def indices05 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 32#u32 5#usize (encodeState value136) 3968#usize
 def indices06 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 36#u32 6#usize (encodeState value137) 4000#usize
 def indices07 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,18#u32,40#u32,43#u32,45#u32,53#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value127,encodeState value128,encodeState value129,encodeState value130]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 40#u32 7#usize (encodeState value138) 4032#usize
 def indices08 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,18#u32,20#u32,43#u32,45#u32,53#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value128,encodeState value129,encodeState value130]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 43#u32 8#usize (encodeState value139) 4064#usize
 def indices09 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,18#u32,20#u32,21#u32,45#u32,53#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value129,encodeState value130]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 45#u32 9#usize (encodeState value140) 4096#usize
 def indices10 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,18#u32,20#u32,21#u32,22#u32,53#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value140,encodeState value130]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 53#u32 10#usize (encodeState value141) 4128#usize
 def indices11 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,18#u32,20#u32,21#u32,22#u32,26#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value140,encodeState value141]
def output (s : reference.Scratch) : reference.Scratch := {s11 s with n:=11#usize}
 def indicesOut : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,18#u32,20#u32,21#u32,22#u32,26#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value131,encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value140,encodeState value141]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3776) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 4128 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3776 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 3#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3776 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value120) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3776 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3776#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠3#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨5#u32,JGm_TX2_View.index (s00 s) indices00 values00 3776 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s00 s).«at» 3808#usize)=ok (encodeState (JGc_TX2_HashBytes.state [118,66,45,191,131,189,214,251,21,46,147,15,77,250,5,72,98,206,157,150,181,2,58,191,80,5,149,160,25,124,36,129])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 118
      4512#usize 3776#usize 3808#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings10.k2c118_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes2 0#usize 0#usize 1#usize 3808#usize 736#usize
    3#u32 (encodeState value120) (encodeState (JGc_TX2_HashBytes.state [118,66,45,191,131,189,214,251,21,46,147,15,77,250,5,72,98,206,157,150,181,2,58,191,80,5,149,160,25,124,36,129])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read00
  simp only [show 3#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls2.source131 D hash (s00 s) 1#usize 3808#usize 3#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3808 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3776 v00
      3#u32 0#usize (encodeState value131) 3808#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 5#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 3808 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value121) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3808 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=3808#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠5#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨10#u32,JGm_TX2_View.index (s01 s) indices01 values01 3808 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s01 s).«at» 3840#usize)=ok (encodeState (JGc_TX2_HashBytes.state [13,182,99,127,33,239,245,120,186,144,205,27,143,155,40,187,1,115,188,146,244,172,189,77,161,204,177,75,200,203,31,114])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 119
      4512#usize 3808#usize 3840#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings10.k2c119_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes2 1#usize 1#usize 2#usize 3840#usize 704#usize
    5#u32 (encodeState value121) (encodeState (JGc_TX2_HashBytes.state [13,182,99,127,33,239,245,120,186,144,205,27,143,155,40,187,1,115,188,146,244,172,189,77,161,204,177,75,200,203,31,114])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read01
  simp only [show 5#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls2.source132 D hash (s01 s) 2#usize 3840#usize 5#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 3840 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 3808 v01
      5#u32 1#usize (encodeState value132) 3840#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 10#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 3840 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value122) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3840 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=3840#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠10#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨13#u32,JGm_TX2_View.index (s02 s) indices02 values02 3840 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s02 s).«at» 3872#usize)=ok (encodeState (JGc_TX2_HashBytes.state [146,164,89,170,7,232,232,36,21,165,44,55,215,245,238,204,47,130,161,56,58,13,100,85,148,93,194,212,175,75,132,243])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 120
      4512#usize 3840#usize 3872#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings10.k2c120_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes2 2#usize 2#usize 3#usize 3872#usize 672#usize
    10#u32 (encodeState value122) (encodeState (JGc_TX2_HashBytes.state [146,164,89,170,7,232,232,36,21,165,44,55,215,245,238,204,47,130,161,56,58,13,100,85,148,93,194,212,175,75,132,243])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read02
  simp only [show 10#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls2.source133 D hash (s02 s) 3#usize 3872#usize 10#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 3872 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 3840 v02
      10#u32 2#usize (encodeState value133) 3872#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 13#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 3872 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value123) :=
    JGm_TX2_View.value (s03 s) indices03 values03 3872 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=3872#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠13#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨15#u32,JGm_TX2_View.index (s03 s) indices03 values03 3872 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s03 s).«at» 3904#usize)=ok (encodeState (JGc_TX2_HashBytes.state [206,135,85,133,68,177,239,151,67,38,254,200,44,43,85,148,131,212,94,195,61,239,118,216,105,79,51,182,62,253,52,13])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 121
      4512#usize 3872#usize 3904#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings10.k2c121_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes2 3#usize 3#usize 4#usize 3904#usize 640#usize
    13#u32 (encodeState value123) (encodeState (JGc_TX2_HashBytes.state [206,135,85,133,68,177,239,151,67,38,254,200,44,43,85,148,131,212,94,195,61,239,118,216,105,79,51,182,62,253,52,13])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read03
  simp only [show 13#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes2 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls2.source134 D hash (s03 s) 4#usize 3904#usize 13#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 3904 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 3872 v03
      13#u32 3#usize (encodeState value134) 3904#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 15#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 3904 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value124) :=
    JGm_TX2_View.value (s04 s) indices04 values04 3904 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=3904#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠15#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨32#u32,JGm_TX2_View.index (s04 s) indices04 values04 3904 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s04 s).«at» 3936#usize)=ok (encodeState (JGc_TX2_HashBytes.state [139,68,231,55,255,62,12,158,36,47,30,226,50,53,120,240,179,138,248,240,27,198,183,236,70,243,193,170,222,73,29,118])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 122
      4512#usize 3904#usize 3936#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings10.k2c122_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes2 4#usize 4#usize 5#usize 3936#usize 608#usize
    15#u32 (encodeState value124) (encodeState (JGc_TX2_HashBytes.state [139,68,231,55,255,62,12,158,36,47,30,226,50,53,120,240,179,138,248,240,27,198,183,236,70,243,193,170,222,73,29,118])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read04
  simp only [show 15#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes2 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls2.source135 D hash (s04 s) 5#usize 3936#usize 15#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 3936 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 3904 v04
      15#u32 4#usize (encodeState value135) 3936#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 32#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 3936 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value125) :=
    JGm_TX2_View.value (s05 s) indices05 values05 3936 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=3936#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠32#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨36#u32,JGm_TX2_View.index (s05 s) indices05 values05 3936 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s05 s).«at» 3968#usize)=ok (encodeState (JGc_TX2_HashBytes.state [40,62,29,29,171,128,93,62,151,133,236,13,67,157,193,122,122,193,249,26,97,185,32,106,101,74,234,215,244,154,188,171])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 123
      4512#usize 3936#usize 3968#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings10.k2c123_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes2 5#usize 5#usize 6#usize 3968#usize 576#usize
    32#u32 (encodeState value125) (encodeState (JGc_TX2_HashBytes.state [40,62,29,29,171,128,93,62,151,133,236,13,67,157,193,122,122,193,249,26,97,185,32,106,101,74,234,215,244,154,188,171])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read05
  simp only [show 32#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes2 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls2.source136 D hash (s05 s) 6#usize 3968#usize 32#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 3968 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 3936 v05
      32#u32 5#usize (encodeState value136) 3968#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 36#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 3968 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value126) :=
    JGm_TX2_View.value (s06 s) indices06 values06 3968 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=3968#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠36#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨40#u32,JGm_TX2_View.index (s06 s) indices06 values06 3968 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s06 s).«at» 4000#usize)=ok (encodeState (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 124
      4512#usize 3968#usize 4000#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings10.k2c124_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes2 6#usize 6#usize 7#usize 4000#usize 544#usize
    36#u32 (encodeState value126) (encodeState (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read06
  simp only [show 36#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes2 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls2.source137 D hash (s06 s) 7#usize 4000#usize 36#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 4000 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 3968 v06
      36#u32 6#usize (encodeState value137) 4000#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 40#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 4000 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value127) :=
    JGm_TX2_View.value (s07 s) indices07 values07 4000 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=4000#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠40#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨43#u32,JGm_TX2_View.index (s07 s) indices07 values07 4000 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s07 s).«at» 4032#usize)=ok (encodeState (JGc_TX2_HashBytes.state [184,10,86,251,254,61,159,179,41,92,94,241,151,243,23,3,198,154,172,68,148,202,189,43,208,185,144,44,251,111,18,170])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 125
      4512#usize 4000#usize 4032#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings10.k2c125_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes2 7#usize 7#usize 8#usize 4032#usize 512#usize
    40#u32 (encodeState value127) (encodeState (JGc_TX2_HashBytes.state [184,10,86,251,254,61,159,179,41,92,94,241,151,243,23,3,198,154,172,68,148,202,189,43,208,185,144,44,251,111,18,170])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read07
  simp only [show 40#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes2 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls2.source138 D hash (s07 s) 8#usize 4032#usize 40#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 4032 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 4000 v07
      40#u32 7#usize (encodeState value138) 4032#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 43#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 4032 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value128) :=
    JGm_TX2_View.value (s08 s) indices08 values08 4032 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=4032#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠43#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨45#u32,JGm_TX2_View.index (s08 s) indices08 values08 4032 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s08 s).«at» 4064#usize)=ok (encodeState (JGc_TX2_HashBytes.state [159,19,201,111,140,252,191,130,202,209,248,162,240,25,45,27,112,122,190,136,102,53,38,21,57,21,29,77,105,239,78,248])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 126
      4512#usize 4032#usize 4064#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings10.k2c126_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes2 8#usize 8#usize 9#usize 4064#usize 480#usize
    43#u32 (encodeState value128) (encodeState (JGc_TX2_HashBytes.state [159,19,201,111,140,252,191,130,202,209,248,162,240,25,45,27,112,122,190,136,102,53,38,21,57,21,29,77,105,239,78,248])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read08
  simp only [show 43#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes2 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls2.source139 D hash (s08 s) 9#usize 4064#usize 43#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 4064 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 4032 v08
      43#u32 8#usize (encodeState value139) 4064#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 45#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 4064 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value129) :=
    JGm_TX2_View.value (s09 s) indices09 values09 4064 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=4064#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠45#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨53#u32,JGm_TX2_View.index (s09 s) indices09 values09 4064 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s09 s).«at» 4096#usize)=ok (encodeState (JGc_TX2_HashBytes.state [94,118,78,239,2,8,1,25,176,182,215,190,219,234,105,116,65,90,245,216,64,126,39,42,42,110,88,104,137,73,20,66])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 127
      4512#usize 4064#usize 4096#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings10.k2c127_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes2 9#usize 9#usize 10#usize 4096#usize 448#usize
    45#u32 (encodeState value129) (encodeState (JGc_TX2_HashBytes.state [94,118,78,239,2,8,1,25,176,182,215,190,219,234,105,116,65,90,245,216,64,126,39,42,42,110,88,104,137,73,20,66])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read09
  simp only [show 45#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes2 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls2.source140 D hash (s09 s) 10#usize 4096#usize 45#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 4096 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 4064 v09
      45#u32 9#usize (encodeState value140) 4096#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 53#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 4096 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value130) :=
    JGm_TX2_View.value (s10 s) indices10 values10 4096 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=4096#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠53#u32 ^^^ 1#u32 := by
    intro more
    change (11:Nat)<(s10 s).n.val at more
    rw [v10.size] at more
    exact False.elim ((by decide : ¬(11:Nat)<11) more)
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s10 s).«at» 4128#usize)=ok (encodeState (JGc_TX2_HashBytes.state [15,137,65,155,185,84,11,183,87,116,45,119,133,164,15,130,191,246,245,116,232,109,27,17,212,41,117,167,202,176,51,212])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 128
      4512#usize 4096#usize 4128#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings10.k2c128_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes2 10#usize 10#usize 11#usize 4128#usize 416#usize
    53#u32 (encodeState value130) (encodeState (JGc_TX2_HashBytes.state [15,137,65,155,185,84,11,183,87,116,45,119,133,164,15,130,191,246,245,116,232,109,27,17,212,41,117,167,202,176,51,212])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read10
  simp only [show 53#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes2 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls2.source141 D hash (s10 s) 11#usize 4128#usize 53#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 4128 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 4096 v10
      53#u32 10#usize (encodeState value141) 4128#usize (by decide)
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
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s11 s).n.val≤11;rw [v11.size];decide)
  · exact JGm_TX2_View.finish (s11 s) indices11 values11 4128
      v11 11#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level2_10
end
