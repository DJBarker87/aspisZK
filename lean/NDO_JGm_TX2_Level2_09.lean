import NDO_JGm_TX2_ParentCalls2
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level2_09
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGc_TX2_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes2
def indices00 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
def values00 : List (Array U8 32#usize) := [encodeState value108,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 6#u32 0#usize (encodeState value120) 3488#usize
 def indices01 : List U32 := [3#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value120,encodeState value109,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 10#u32 1#usize (encodeState value121) 3520#usize
 def indices02 : List U32 := [3#u32,5#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value110,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 20#u32 2#usize (encodeState value122) 3552#usize
 def indices03 : List U32 := [3#u32,5#u32,10#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value111,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 27#u32 3#usize (encodeState value123) 3584#usize
 def indices04 : List U32 := [3#u32,5#u32,10#u32,13#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value112,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 31#u32 4#usize (encodeState value124) 3616#usize
 def indices05 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value113,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 64#u32 5#usize (encodeState value125) 3648#usize
 def indices06 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value114,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 73#u32 6#usize (encodeState value126) 3680#usize
 def indices07 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value115,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 81#u32 7#usize (encodeState value127) 3712#usize
 def indices08 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,86#u32,87#u32,90#u32,106#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value116,encodeState value117,encodeState value118,encodeState value119]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 86#u32 8#usize (encodeState value128) 3712#usize
 def indices09 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,87#u32,90#u32,106#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value117,encodeState value118,encodeState value119]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 90#u32 9#usize (encodeState value129) 3744#usize
 def indices10 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,90#u32,106#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value118,encodeState value119]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 106#u32 10#usize (encodeState value130) 3776#usize
 def indices11 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32,106#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130,encodeState value119]
def output (s : reference.Scratch) : reference.Scratch := {s11 s with n:=11#usize}
 def indicesOut : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value120,encodeState value121,encodeState value122,encodeState value123,encodeState value124,encodeState value125,encodeState value126,encodeState value127,encodeState value128,encodeState value129,encodeState value130]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 3456) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 3776 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 3456 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 6#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 3456 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value108) :=
    JGm_TX2_View.value (s00 s) indices00 values00 3456 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=3456#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠6#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨10#u32,JGm_TX2_View.index (s00 s) indices00 values00 3456 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s00 s).«at» 3488#usize)=ok (encodeState (JGc_TX2_HashBytes.state [168,7,249,118,41,85,216,10,25,159,158,171,90,187,183,16,118,37,5,65,104,46,122,46,48,223,68,164,178,237,132,147])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 108
      4512#usize 3456#usize 3488#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings09.k2c108_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes2 0#usize 0#usize 1#usize 3488#usize 1056#usize
    6#u32 (encodeState value108) (encodeState (JGc_TX2_HashBytes.state [168,7,249,118,41,85,216,10,25,159,158,171,90,187,183,16,118,37,5,65,104,46,122,46,48,223,68,164,178,237,132,147])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read00
  simp only [show 6#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls2.source120 D hash (s00 s) 1#usize 3488#usize 6#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 3488 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 3456 v00
      6#u32 0#usize (encodeState value120) 3488#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 10#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 3488 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value109) :=
    JGm_TX2_View.value (s01 s) indices01 values01 3488 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=3488#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠10#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨20#u32,JGm_TX2_View.index (s01 s) indices01 values01 3488 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s01 s).«at» 3520#usize)=ok (encodeState (JGc_TX2_HashBytes.state [223,110,19,245,244,227,40,27,81,156,133,231,100,90,222,155,141,223,74,73,201,135,68,137,159,19,105,243,31,9,14,253])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 109
      4512#usize 3488#usize 3520#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings09.k2c109_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes2 1#usize 1#usize 2#usize 3520#usize 1024#usize
    10#u32 (encodeState value109) (encodeState (JGc_TX2_HashBytes.state [223,110,19,245,244,227,40,27,81,156,133,231,100,90,222,155,141,223,74,73,201,135,68,137,159,19,105,243,31,9,14,253])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read01
  simp only [show 10#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls2.source121 D hash (s01 s) 2#usize 3520#usize 10#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 3520 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 3488 v01
      10#u32 1#usize (encodeState value121) 3520#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 20#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 3520 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value110) :=
    JGm_TX2_View.value (s02 s) indices02 values02 3520 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=3520#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠20#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨27#u32,JGm_TX2_View.index (s02 s) indices02 values02 3520 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s02 s).«at» 3552#usize)=ok (encodeState (JGc_TX2_HashBytes.state [102,114,57,147,28,89,57,26,132,252,183,78,113,182,85,171,1,134,183,8,61,123,243,13,61,142,238,93,184,41,34,9])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 110
      4512#usize 3520#usize 3552#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings09.k2c110_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes2 2#usize 2#usize 3#usize 3552#usize 992#usize
    20#u32 (encodeState value110) (encodeState (JGc_TX2_HashBytes.state [102,114,57,147,28,89,57,26,132,252,183,78,113,182,85,171,1,134,183,8,61,123,243,13,61,142,238,93,184,41,34,9])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read02
  simp only [show 20#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls2.source122 D hash (s02 s) 3#usize 3552#usize 20#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 3552 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 3520 v02
      20#u32 2#usize (encodeState value122) 3552#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 27#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 3552 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value111) :=
    JGm_TX2_View.value (s03 s) indices03 values03 3552 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=3552#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠27#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨31#u32,JGm_TX2_View.index (s03 s) indices03 values03 3552 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s03 s).«at» 3584#usize)=ok (encodeState (JGc_TX2_HashBytes.state [30,144,71,74,223,163,141,159,44,118,14,152,185,148,50,186,42,1,84,96,23,18,151,25,103,4,194,17,226,166,15,229])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 111
      4512#usize 3552#usize 3584#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings09.k2c111_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes2 3#usize 3#usize 4#usize 3584#usize 960#usize
    27#u32 (encodeState value111) (encodeState (JGc_TX2_HashBytes.state [30,144,71,74,223,163,141,159,44,118,14,152,185,148,50,186,42,1,84,96,23,18,151,25,103,4,194,17,226,166,15,229])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read03
  simp only [show 27#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes2 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls2.source123 D hash (s03 s) 4#usize 3584#usize 27#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 3584 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 3552 v03
      27#u32 3#usize (encodeState value123) 3584#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 31#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 3584 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value112) :=
    JGm_TX2_View.value (s04 s) indices04 values04 3584 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=3584#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠31#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨64#u32,JGm_TX2_View.index (s04 s) indices04 values04 3584 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s04 s).«at» 3616#usize)=ok (encodeState (JGc_TX2_HashBytes.state [168,185,27,215,169,143,230,34,123,226,41,203,176,173,35,86,15,160,129,187,149,85,125,69,74,221,167,0,254,58,246,97])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 112
      4512#usize 3584#usize 3616#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings09.k2c112_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes2 4#usize 4#usize 5#usize 3616#usize 928#usize
    31#u32 (encodeState value112) (encodeState (JGc_TX2_HashBytes.state [168,185,27,215,169,143,230,34,123,226,41,203,176,173,35,86,15,160,129,187,149,85,125,69,74,221,167,0,254,58,246,97])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read04
  simp only [show 31#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes2 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls2.source124 D hash (s04 s) 5#usize 3616#usize 31#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 3616 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 3584 v04
      31#u32 4#usize (encodeState value124) 3616#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 64#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 3616 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value113) :=
    JGm_TX2_View.value (s05 s) indices05 values05 3616 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=3616#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠64#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨73#u32,JGm_TX2_View.index (s05 s) indices05 values05 3616 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s05 s).«at» 3648#usize)=ok (encodeState (JGc_TX2_HashBytes.state [85,52,188,98,167,123,66,214,196,173,57,251,166,199,135,77,137,4,18,137,157,63,245,131,127,145,115,65,11,17,98,86])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 113
      4512#usize 3616#usize 3648#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings09.k2c113_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes2 5#usize 5#usize 6#usize 3648#usize 896#usize
    64#u32 (encodeState value113) (encodeState (JGc_TX2_HashBytes.state [85,52,188,98,167,123,66,214,196,173,57,251,166,199,135,77,137,4,18,137,157,63,245,131,127,145,115,65,11,17,98,86])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read05
  simp only [show 64#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes2 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls2.source125 D hash (s05 s) 6#usize 3648#usize 64#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 3648 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 3616 v05
      64#u32 5#usize (encodeState value125) 3648#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 73#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 3648 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value114) :=
    JGm_TX2_View.value (s06 s) indices06 values06 3648 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=3648#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠73#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨81#u32,JGm_TX2_View.index (s06 s) indices06 values06 3648 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s06 s).«at» 3680#usize)=ok (encodeState (JGc_TX2_HashBytes.state [3,169,173,149,56,183,16,65,144,251,102,110,90,130,50,162,198,79,206,71,140,144,205,72,79,12,148,87,5,250,183,64])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 114
      4512#usize 3648#usize 3680#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings09.k2c114_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes2 6#usize 6#usize 7#usize 3680#usize 864#usize
    73#u32 (encodeState value114) (encodeState (JGc_TX2_HashBytes.state [3,169,173,149,56,183,16,65,144,251,102,110,90,130,50,162,198,79,206,71,140,144,205,72,79,12,148,87,5,250,183,64])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read06
  simp only [show 73#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes2 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls2.source126 D hash (s06 s) 7#usize 3680#usize 73#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 3680 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 3648 v06
      73#u32 6#usize (encodeState value126) 3680#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 81#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 3680 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value115) :=
    JGm_TX2_View.value (s07 s) indices07 values07 3680 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=3680#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠81#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨86#u32,JGm_TX2_View.index (s07 s) indices07 values07 3680 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s07 s).«at» 3712#usize)=ok (encodeState (JGc_TX2_HashBytes.state [68,142,32,219,36,14,61,147,63,76,253,213,15,49,48,199,103,187,177,232,161,155,25,243,47,133,3,49,103,196,177,80])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 115
      4512#usize 3680#usize 3712#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings09.k2c115_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes2 7#usize 7#usize 8#usize 3712#usize 832#usize
    81#u32 (encodeState value115) (encodeState (JGc_TX2_HashBytes.state [68,142,32,219,36,14,61,147,63,76,253,213,15,49,48,199,103,187,177,232,161,155,25,243,47,133,3,49,103,196,177,80])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read07
  simp only [show 81#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes2 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls2.source127 D hash (s07 s) 8#usize 3712#usize 81#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 3712 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 3680 v07
      81#u32 7#usize (encodeState value127) 3712#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 86#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 3712 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value116) :=
    JGm_TX2_View.value (s08 s) indices08 values08 3712 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=3712#usize := UScalar.eq_of_val_eq v08.at_eq
  have rn08 : Array.index_usize (s08 s).idx 9#usize=ok (86#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s08 s) indices08 values08 3712 v08 9#usize (by decide)
  have rr08 : Array.index_usize (s08 s).val 9#usize=ok (encodeState value117) :=
    JGm_TX2_View.value (s08 s) indices08 values08 3712 v08 9#usize (by decide)
  have selected08 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes2 8#usize 8#usize 9#usize 10#usize 86#u32
    (encodeState value116) (encodeState value117) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (9:Nat)<(s08 s).n.val;rw [v08.size];decide)
    rn08 rr08 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes2 8#usize 8#usize=
        ok (.Next (s09 s) 10#usize 9#usize) := by
    rw [selected08]
    rw [cursor08]
    exact JGm_TX2_ParentCalls2.source128 D hash (s08 s) 10#usize 3712#usize 86#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 3712 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 3712 v08
      86#u32 8#usize (encodeState value128) 3712#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 10#usize=ok 90#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 3712 v09 10#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 10#usize=ok (encodeState value118) :=
    JGm_TX2_View.value (s09 s) indices09 values09 3712 v09 10#usize (by decide)
  have active09 : 10#usize<(s09 s).n := by
    change (10:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=3712#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 11#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 11#usize=ok other ∧ other≠90#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨106#u32,JGm_TX2_View.index (s09 s) indices09 values09 3712 v09 11#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s09 s).«at» 3744#usize)=ok (encodeState (JGc_TX2_HashBytes.state [234,157,205,160,100,45,156,15,124,40,37,125,157,253,108,73,107,187,203,131,100,153,6,19,58,141,158,46,248,238,239,168])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 116
      4512#usize 3712#usize 3744#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings09.k2c116_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes2 10#usize 9#usize 11#usize 3744#usize 800#usize
    90#u32 (encodeState value118) (encodeState (JGc_TX2_HashBytes.state [234,157,205,160,100,45,156,15,124,40,37,125,157,253,108,73,107,187,203,131,100,153,6,19,58,141,158,46,248,238,239,168])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read09
  simp only [show 90#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes2 10#usize 9#usize=
        ok (.Next (s10 s) 11#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls2.source129 D hash (s09 s) 11#usize 3744#usize 90#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 3744 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 3712 v09
      90#u32 9#usize (encodeState value129) 3744#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 11#usize=ok 106#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 3744 v10 11#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 11#usize=ok (encodeState value119) :=
    JGm_TX2_View.value (s10 s) indices10 values10 3744 v10 11#usize (by decide)
  have active10 : 11#usize<(s10 s).n := by
    change (11:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=3744#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 12#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 12#usize=ok other ∧ other≠106#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s10 s).n.val at more
    rw [v10.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes2
      (s10 s).«at» 3776#usize)=ok (encodeState (JGc_TX2_HashBytes.state [236,197,164,41,198,181,226,108,46,53,158,12,123,51,246,145,217,190,204,61,35,251,196,98,163,57,138,148,20,238,77,232])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes2 117
      4512#usize 3744#usize 3776#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length2];decide)
    rw [JGh_TX2_Siblings09.k2c117_read] at read
    simpa only [JGm_TX2_Supplied.nodes2,JGc_TX2_M2Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes2 11#usize 10#usize 12#usize 3776#usize 768#usize
    106#u32 (encodeState value119) (encodeState (JGc_TX2_HashBytes.state [236,197,164,41,198,181,226,108,46,53,158,12,123,51,246,145,217,190,204,61,35,251,196,98,163,57,138,148,20,238,77,232])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length2];decide) read10
  simp only [show 106#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes2 11#usize 10#usize=
        ok (.Next (s11 s) 12#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls2.source130 D hash (s10 s) 12#usize 3776#usize 106#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 3776 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 3744 v10
      106#u32 10#usize (encodeState value130) 3776#usize (by decide)
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
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGm_TX2_Supplied.nodes2 10#usize 9#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGm_TX2_Supplied.nodes2 11#usize 10#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s) JGm_TX2_Supplied.nodes2 12#usize 11#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active10 row10
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s11 s).n.val≤12;rw [v11.size];decide)
  · exact JGm_TX2_View.finish (s11 s) indices11 values11 3776
      v11 11#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level2_09
end
