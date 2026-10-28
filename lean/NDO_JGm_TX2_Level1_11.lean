import NDO_JGm_TX2_ParentCalls1
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level1_11
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGh_TX2_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes1
def indices00 : List U32 := [6#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
def values00 : List (Array U8 32#usize) := [encodeState value132,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 6#u32 0#usize (encodeState value144) 4256#usize
 def indices01 : List U32 := [3#u32,10#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value144,encodeState value133,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 10#u32 1#usize (encodeState value145) 4288#usize
 def indices02 : List U32 := [3#u32,5#u32,20#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value144,encodeState value145,encodeState value134,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 20#u32 2#usize (encodeState value146) 4320#usize
 def indices03 : List U32 := [3#u32,5#u32,10#u32,27#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value144,encodeState value145,encodeState value146,encodeState value135,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 27#u32 3#usize (encodeState value147) 4352#usize
 def indices04 : List U32 := [3#u32,5#u32,10#u32,13#u32,31#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value144,encodeState value145,encodeState value146,encodeState value147,encodeState value136,encodeState value137,encodeState value138,encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 31#u32 4#usize (encodeState value148) 4384#usize
 def indices05 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,64#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value144,encodeState value145,encodeState value146,encodeState value147,encodeState value148,encodeState value137,encodeState value138,encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 64#u32 5#usize (encodeState value149) 4416#usize
 def indices06 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,73#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value144,encodeState value145,encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value138,encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 73#u32 6#usize (encodeState value150) 4448#usize
 def indices07 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,81#u32,86#u32,87#u32,90#u32,106#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value144,encodeState value145,encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150,encodeState value139,encodeState value140,encodeState value141,encodeState value142,encodeState value143]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 81#u32 7#usize (encodeState value151) 4480#usize
 def indices08 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,86#u32,87#u32,90#u32,106#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value144,encodeState value145,encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150,encodeState value151,encodeState value140,encodeState value141,encodeState value142,encodeState value143]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 86#u32 8#usize (encodeState value152) 4480#usize
 def indices09 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,87#u32,90#u32,106#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value144,encodeState value145,encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150,encodeState value151,encodeState value152,encodeState value141,encodeState value142,encodeState value143]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 90#u32 9#usize (encodeState value153) 4512#usize
 def indices10 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,90#u32,106#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value144,encodeState value145,encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150,encodeState value151,encodeState value152,encodeState value153,encodeState value142,encodeState value143]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 106#u32 10#usize (encodeState value154) 4544#usize
 def indices11 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32,106#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value144,encodeState value145,encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150,encodeState value151,encodeState value152,encodeState value153,encodeState value154,encodeState value143]
def output (s : reference.Scratch) : reference.Scratch := {s11 s with n:=11#usize}
 def indicesOut : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value144,encodeState value145,encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150,encodeState value151,encodeState value152,encodeState value153,encodeState value154]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 4224) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 4544 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 4224 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 6#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 4224 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value132) :=
    JGm_TX2_View.value (s00 s) indices00 values00 4224 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=4224#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠6#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨10#u32,JGm_TX2_View.index (s00 s) indices00 values00 4224 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s00 s).«at» 4256#usize)=ok (encodeState (JGc_TX2_HashBytes.state [143,199,204,55,253,98,13,22,190,146,1,216,157,72,105,32,67,164,206,221,6,70,2,195,111,189,13,28,87,240,124,9])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 132
      5216#usize 4224#usize 4256#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings11.k1c132_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes1 0#usize 0#usize 1#usize 4256#usize 992#usize
    6#u32 (encodeState value132) (encodeState (JGc_TX2_HashBytes.state [143,199,204,55,253,98,13,22,190,146,1,216,157,72,105,32,67,164,206,221,6,70,2,195,111,189,13,28,87,240,124,9])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read00
  simp only [show 6#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls1.source144 D hash (s00 s) 1#usize 4256#usize 6#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 4256 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 4224 v00
      6#u32 0#usize (encodeState value144) 4256#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 10#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 4256 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value133) :=
    JGm_TX2_View.value (s01 s) indices01 values01 4256 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=4256#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠10#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨20#u32,JGm_TX2_View.index (s01 s) indices01 values01 4256 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s01 s).«at» 4288#usize)=ok (encodeState (JGc_TX2_HashBytes.state [160,190,50,192,195,44,146,136,171,14,31,33,226,231,207,222,139,191,178,90,242,241,206,240,176,102,107,97,79,158,215,23])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 133
      5216#usize 4256#usize 4288#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings11.k1c133_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes1 1#usize 1#usize 2#usize 4288#usize 960#usize
    10#u32 (encodeState value133) (encodeState (JGc_TX2_HashBytes.state [160,190,50,192,195,44,146,136,171,14,31,33,226,231,207,222,139,191,178,90,242,241,206,240,176,102,107,97,79,158,215,23])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read01
  simp only [show 10#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls1.source145 D hash (s01 s) 2#usize 4288#usize 10#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 4288 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 4256 v01
      10#u32 1#usize (encodeState value145) 4288#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 20#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 4288 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value134) :=
    JGm_TX2_View.value (s02 s) indices02 values02 4288 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=4288#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠20#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨27#u32,JGm_TX2_View.index (s02 s) indices02 values02 4288 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s02 s).«at» 4320#usize)=ok (encodeState (JGc_TX2_HashBytes.state [208,188,33,108,119,232,59,31,139,120,97,178,191,254,61,140,25,177,89,169,31,36,93,222,180,203,69,206,79,131,113,119])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 134
      5216#usize 4288#usize 4320#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings11.k1c134_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes1 2#usize 2#usize 3#usize 4320#usize 928#usize
    20#u32 (encodeState value134) (encodeState (JGc_TX2_HashBytes.state [208,188,33,108,119,232,59,31,139,120,97,178,191,254,61,140,25,177,89,169,31,36,93,222,180,203,69,206,79,131,113,119])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read02
  simp only [show 20#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls1.source146 D hash (s02 s) 3#usize 4320#usize 20#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 4320 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 4288 v02
      20#u32 2#usize (encodeState value146) 4320#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 27#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 4320 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value135) :=
    JGm_TX2_View.value (s03 s) indices03 values03 4320 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=4320#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠27#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨31#u32,JGm_TX2_View.index (s03 s) indices03 values03 4320 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s03 s).«at» 4352#usize)=ok (encodeState (JGc_TX2_HashBytes.state [52,242,58,52,243,87,131,83,79,58,254,97,66,106,22,24,133,152,32,239,114,132,152,63,133,15,72,220,26,92,140,225])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 135
      5216#usize 4320#usize 4352#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings11.k1c135_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes1 3#usize 3#usize 4#usize 4352#usize 896#usize
    27#u32 (encodeState value135) (encodeState (JGc_TX2_HashBytes.state [52,242,58,52,243,87,131,83,79,58,254,97,66,106,22,24,133,152,32,239,114,132,152,63,133,15,72,220,26,92,140,225])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read03
  simp only [show 27#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls1.source147 D hash (s03 s) 4#usize 4352#usize 27#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 4352 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 4320 v03
      27#u32 3#usize (encodeState value147) 4352#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 31#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 4352 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value136) :=
    JGm_TX2_View.value (s04 s) indices04 values04 4352 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=4352#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠31#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨64#u32,JGm_TX2_View.index (s04 s) indices04 values04 4352 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s04 s).«at» 4384#usize)=ok (encodeState (JGc_TX2_HashBytes.state [142,177,4,242,28,255,193,231,213,28,174,2,120,159,200,153,91,208,243,67,18,171,247,254,156,220,73,169,103,78,35,206])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 136
      5216#usize 4352#usize 4384#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings11.k1c136_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes1 4#usize 4#usize 5#usize 4384#usize 864#usize
    31#u32 (encodeState value136) (encodeState (JGc_TX2_HashBytes.state [142,177,4,242,28,255,193,231,213,28,174,2,120,159,200,153,91,208,243,67,18,171,247,254,156,220,73,169,103,78,35,206])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read04
  simp only [show 31#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls1.source148 D hash (s04 s) 5#usize 4384#usize 31#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 4384 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 4352 v04
      31#u32 4#usize (encodeState value148) 4384#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 64#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 4384 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value137) :=
    JGm_TX2_View.value (s05 s) indices05 values05 4384 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=4384#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠64#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨73#u32,JGm_TX2_View.index (s05 s) indices05 values05 4384 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s05 s).«at» 4416#usize)=ok (encodeState (JGc_TX2_HashBytes.state [60,247,162,3,152,178,85,100,187,241,133,191,8,182,206,157,149,167,144,55,142,56,196,48,89,183,252,64,90,150,82,73])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 137
      5216#usize 4384#usize 4416#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings11.k1c137_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes1 5#usize 5#usize 6#usize 4416#usize 832#usize
    64#u32 (encodeState value137) (encodeState (JGc_TX2_HashBytes.state [60,247,162,3,152,178,85,100,187,241,133,191,8,182,206,157,149,167,144,55,142,56,196,48,89,183,252,64,90,150,82,73])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read05
  simp only [show 64#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls1.source149 D hash (s05 s) 6#usize 4416#usize 64#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 4416 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 4384 v05
      64#u32 5#usize (encodeState value149) 4416#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 73#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 4416 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value138) :=
    JGm_TX2_View.value (s06 s) indices06 values06 4416 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=4416#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠73#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨81#u32,JGm_TX2_View.index (s06 s) indices06 values06 4416 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s06 s).«at» 4448#usize)=ok (encodeState (JGc_TX2_HashBytes.state [190,221,229,205,197,195,172,22,103,65,29,2,92,130,215,93,98,222,51,68,174,92,227,55,144,218,246,177,154,144,188,114])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 138
      5216#usize 4416#usize 4448#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings11.k1c138_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes1 6#usize 6#usize 7#usize 4448#usize 800#usize
    73#u32 (encodeState value138) (encodeState (JGc_TX2_HashBytes.state [190,221,229,205,197,195,172,22,103,65,29,2,92,130,215,93,98,222,51,68,174,92,227,55,144,218,246,177,154,144,188,114])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read06
  simp only [show 73#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls1.source150 D hash (s06 s) 7#usize 4448#usize 73#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 4448 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 4416 v06
      73#u32 6#usize (encodeState value150) 4448#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 81#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 4448 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value139) :=
    JGm_TX2_View.value (s07 s) indices07 values07 4448 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=4448#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠81#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨86#u32,JGm_TX2_View.index (s07 s) indices07 values07 4448 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s07 s).«at» 4480#usize)=ok (encodeState (JGc_TX2_HashBytes.state [3,20,237,12,251,196,101,208,64,164,161,71,157,1,255,107,220,196,111,236,239,55,118,41,159,30,219,170,84,247,138,34])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 139
      5216#usize 4448#usize 4480#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings11.k1c139_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes1 7#usize 7#usize 8#usize 4480#usize 768#usize
    81#u32 (encodeState value139) (encodeState (JGc_TX2_HashBytes.state [3,20,237,12,251,196,101,208,64,164,161,71,157,1,255,107,220,196,111,236,239,55,118,41,159,30,219,170,84,247,138,34])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read07
  simp only [show 81#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls1.source151 D hash (s07 s) 8#usize 4480#usize 81#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 4480 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 4448 v07
      81#u32 7#usize (encodeState value151) 4480#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 86#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 4480 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value140) :=
    JGm_TX2_View.value (s08 s) indices08 values08 4480 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=4480#usize := UScalar.eq_of_val_eq v08.at_eq
  have rn08 : Array.index_usize (s08 s).idx 9#usize=ok (86#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s08 s) indices08 values08 4480 v08 9#usize (by decide)
  have rr08 : Array.index_usize (s08 s).val 9#usize=ok (encodeState value141) :=
    JGm_TX2_View.value (s08 s) indices08 values08 4480 v08 9#usize (by decide)
  have selected08 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes1 8#usize 8#usize 9#usize 10#usize 86#u32
    (encodeState value140) (encodeState value141) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (9:Nat)<(s08 s).n.val;rw [v08.size];decide)
    rn08 rr08 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 10#usize 9#usize) := by
    rw [selected08]
    rw [cursor08]
    exact JGm_TX2_ParentCalls1.source152 D hash (s08 s) 10#usize 4480#usize 86#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 4480 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 4480 v08
      86#u32 8#usize (encodeState value152) 4480#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 10#usize=ok 90#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 4480 v09 10#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 10#usize=ok (encodeState value142) :=
    JGm_TX2_View.value (s09 s) indices09 values09 4480 v09 10#usize (by decide)
  have active09 : 10#usize<(s09 s).n := by
    change (10:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=4480#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 11#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 11#usize=ok other ∧ other≠90#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨106#u32,JGm_TX2_View.index (s09 s) indices09 values09 4480 v09 11#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s09 s).«at» 4512#usize)=ok (encodeState (JGc_TX2_HashBytes.state [203,121,174,182,41,152,36,76,14,113,249,132,254,32,196,147,61,212,161,165,109,165,45,139,128,114,11,126,152,236,58,158])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 140
      5216#usize 4480#usize 4512#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings11.k1c140_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes1 10#usize 9#usize 11#usize 4512#usize 736#usize
    90#u32 (encodeState value142) (encodeState (JGc_TX2_HashBytes.state [203,121,174,182,41,152,36,76,14,113,249,132,254,32,196,147,61,212,161,165,109,165,45,139,128,114,11,126,152,236,58,158])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read09
  simp only [show 90#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes1 10#usize 9#usize=
        ok (.Next (s10 s) 11#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls1.source153 D hash (s09 s) 11#usize 4512#usize 90#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 4512 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 4480 v09
      90#u32 9#usize (encodeState value153) 4512#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 11#usize=ok 106#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 4512 v10 11#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 11#usize=ok (encodeState value143) :=
    JGm_TX2_View.value (s10 s) indices10 values10 4512 v10 11#usize (by decide)
  have active10 : 11#usize<(s10 s).n := by
    change (11:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=4512#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 12#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 12#usize=ok other ∧ other≠106#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s10 s).n.val at more
    rw [v10.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s10 s).«at» 4544#usize)=ok (encodeState (JGc_TX2_HashBytes.state [247,175,29,17,115,110,241,39,140,154,188,14,136,255,55,135,243,53,60,49,253,175,182,64,108,10,86,95,219,100,20,110])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 141
      5216#usize 4512#usize 4544#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings11.k1c141_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes1 11#usize 10#usize 12#usize 4544#usize 704#usize
    106#u32 (encodeState value143) (encodeState (JGc_TX2_HashBytes.state [247,175,29,17,115,110,241,39,140,154,188,14,136,255,55,135,243,53,60,49,253,175,182,64,108,10,86,95,219,100,20,110])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read10
  simp only [show 106#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes1 11#usize 10#usize=
        ok (.Next (s11 s) 12#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls1.source154 D hash (s10 s) 12#usize 4544#usize 106#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 4544 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 4512 v10
      106#u32 10#usize (encodeState value154) 4544#usize (by decide)
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
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGm_TX2_Supplied.nodes1 10#usize 9#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGm_TX2_Supplied.nodes1 11#usize 10#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s) JGm_TX2_Supplied.nodes1 12#usize 11#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active10 row10
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s11 s).n.val≤12;rw [v11.size];decide)
  · exact JGm_TX2_View.finish (s11 s) indices11 values11 4544
      v11 11#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level1_11
end
