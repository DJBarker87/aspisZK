import NDO_JGm_TX2_ParentCalls1
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level1_12
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGh_TX2_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes1
def indices00 : List U32 := [3#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
def values00 : List (Array U8 32#usize) := [encodeState value144,encodeState value145,encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150,encodeState value151,encodeState value152,encodeState value153,encodeState value154]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 3#u32 0#usize (encodeState value155) 4576#usize
 def indices01 : List U32 := [1#u32,5#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value155,encodeState value145,encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150,encodeState value151,encodeState value152,encodeState value153,encodeState value154]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 5#u32 1#usize (encodeState value156) 4608#usize
 def indices02 : List U32 := [1#u32,2#u32,10#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value155,encodeState value156,encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150,encodeState value151,encodeState value152,encodeState value153,encodeState value154]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 10#u32 2#usize (encodeState value157) 4640#usize
 def indices03 : List U32 := [1#u32,2#u32,5#u32,13#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value155,encodeState value156,encodeState value157,encodeState value147,encodeState value148,encodeState value149,encodeState value150,encodeState value151,encodeState value152,encodeState value153,encodeState value154]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 13#u32 3#usize (encodeState value158) 4672#usize
 def indices04 : List U32 := [1#u32,2#u32,5#u32,6#u32,15#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value155,encodeState value156,encodeState value157,encodeState value158,encodeState value148,encodeState value149,encodeState value150,encodeState value151,encodeState value152,encodeState value153,encodeState value154]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 15#u32 4#usize (encodeState value159) 4704#usize
 def indices05 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,32#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value155,encodeState value156,encodeState value157,encodeState value158,encodeState value159,encodeState value149,encodeState value150,encodeState value151,encodeState value152,encodeState value153,encodeState value154]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 32#u32 5#usize (encodeState value160) 4736#usize
 def indices06 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,36#u32,40#u32,43#u32,45#u32,53#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value155,encodeState value156,encodeState value157,encodeState value158,encodeState value159,encodeState value160,encodeState value150,encodeState value151,encodeState value152,encodeState value153,encodeState value154]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 36#u32 6#usize (encodeState value161) 4768#usize
 def indices07 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,18#u32,40#u32,43#u32,45#u32,53#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value155,encodeState value156,encodeState value157,encodeState value158,encodeState value159,encodeState value160,encodeState value161,encodeState value151,encodeState value152,encodeState value153,encodeState value154]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 40#u32 7#usize (encodeState value162) 4800#usize
 def indices08 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,18#u32,20#u32,43#u32,45#u32,53#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value155,encodeState value156,encodeState value157,encodeState value158,encodeState value159,encodeState value160,encodeState value161,encodeState value162,encodeState value152,encodeState value153,encodeState value154]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 43#u32 8#usize (encodeState value163) 4832#usize
 def indices09 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,18#u32,20#u32,21#u32,45#u32,53#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value155,encodeState value156,encodeState value157,encodeState value158,encodeState value159,encodeState value160,encodeState value161,encodeState value162,encodeState value163,encodeState value153,encodeState value154]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 45#u32 9#usize (encodeState value164) 4864#usize
 def indices10 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,18#u32,20#u32,21#u32,22#u32,53#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value155,encodeState value156,encodeState value157,encodeState value158,encodeState value159,encodeState value160,encodeState value161,encodeState value162,encodeState value163,encodeState value164,encodeState value154]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 53#u32 10#usize (encodeState value165) 4896#usize
 def indices11 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,18#u32,20#u32,21#u32,22#u32,26#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value155,encodeState value156,encodeState value157,encodeState value158,encodeState value159,encodeState value160,encodeState value161,encodeState value162,encodeState value163,encodeState value164,encodeState value165]
def output (s : reference.Scratch) : reference.Scratch := {s11 s with n:=11#usize}
 def indicesOut : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,18#u32,20#u32,21#u32,22#u32,26#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value155,encodeState value156,encodeState value157,encodeState value158,encodeState value159,encodeState value160,encodeState value161,encodeState value162,encodeState value163,encodeState value164,encodeState value165]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 4544) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 4896 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 4544 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 3#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 4544 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value144) :=
    JGm_TX2_View.value (s00 s) indices00 values00 4544 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=4544#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠3#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨5#u32,JGm_TX2_View.index (s00 s) indices00 values00 4544 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s00 s).«at» 4576#usize)=ok (encodeState (JGc_TX2_HashBytes.state [88,200,200,81,100,47,155,128,194,217,234,133,129,18,210,1,199,237,115,41,149,114,203,147,5,111,43,248,223,43,115,216])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 142
      5216#usize 4544#usize 4576#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings12.k1c142_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes1 0#usize 0#usize 1#usize 4576#usize 672#usize
    3#u32 (encodeState value144) (encodeState (JGc_TX2_HashBytes.state [88,200,200,81,100,47,155,128,194,217,234,133,129,18,210,1,199,237,115,41,149,114,203,147,5,111,43,248,223,43,115,216])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read00
  simp only [show 3#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls1.source155 D hash (s00 s) 1#usize 4576#usize 3#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 4576 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 4544 v00
      3#u32 0#usize (encodeState value155) 4576#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 5#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 4576 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value145) :=
    JGm_TX2_View.value (s01 s) indices01 values01 4576 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=4576#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠5#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨10#u32,JGm_TX2_View.index (s01 s) indices01 values01 4576 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s01 s).«at» 4608#usize)=ok (encodeState (JGc_TX2_HashBytes.state [79,108,89,128,240,221,233,127,228,95,64,148,219,84,123,220,220,94,159,117,164,89,181,53,206,197,95,79,70,7,116,207])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 143
      5216#usize 4576#usize 4608#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings12.k1c143_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes1 1#usize 1#usize 2#usize 4608#usize 640#usize
    5#u32 (encodeState value145) (encodeState (JGc_TX2_HashBytes.state [79,108,89,128,240,221,233,127,228,95,64,148,219,84,123,220,220,94,159,117,164,89,181,53,206,197,95,79,70,7,116,207])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read01
  simp only [show 5#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls1.source156 D hash (s01 s) 2#usize 4608#usize 5#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 4608 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 4576 v01
      5#u32 1#usize (encodeState value156) 4608#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 10#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 4608 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value146) :=
    JGm_TX2_View.value (s02 s) indices02 values02 4608 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=4608#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠10#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨13#u32,JGm_TX2_View.index (s02 s) indices02 values02 4608 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s02 s).«at» 4640#usize)=ok (encodeState (JGc_TX2_HashBytes.state [74,28,108,176,140,202,10,70,55,105,207,14,98,39,31,53,103,54,134,75,220,181,149,104,222,170,139,72,19,184,148,224])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 144
      5216#usize 4608#usize 4640#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings12.k1c144_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes1 2#usize 2#usize 3#usize 4640#usize 608#usize
    10#u32 (encodeState value146) (encodeState (JGc_TX2_HashBytes.state [74,28,108,176,140,202,10,70,55,105,207,14,98,39,31,53,103,54,134,75,220,181,149,104,222,170,139,72,19,184,148,224])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read02
  simp only [show 10#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls1.source157 D hash (s02 s) 3#usize 4640#usize 10#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 4640 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 4608 v02
      10#u32 2#usize (encodeState value157) 4640#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 13#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 4640 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value147) :=
    JGm_TX2_View.value (s03 s) indices03 values03 4640 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=4640#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠13#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨15#u32,JGm_TX2_View.index (s03 s) indices03 values03 4640 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s03 s).«at» 4672#usize)=ok (encodeState (JGc_TX2_HashBytes.state [180,193,203,72,70,35,220,107,55,36,139,66,87,30,135,220,78,200,66,26,142,34,206,196,104,172,191,246,63,199,196,214])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 145
      5216#usize 4640#usize 4672#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings12.k1c145_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes1 3#usize 3#usize 4#usize 4672#usize 576#usize
    13#u32 (encodeState value147) (encodeState (JGc_TX2_HashBytes.state [180,193,203,72,70,35,220,107,55,36,139,66,87,30,135,220,78,200,66,26,142,34,206,196,104,172,191,246,63,199,196,214])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read03
  simp only [show 13#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls1.source158 D hash (s03 s) 4#usize 4672#usize 13#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 4672 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 4640 v03
      13#u32 3#usize (encodeState value158) 4672#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 15#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 4672 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value148) :=
    JGm_TX2_View.value (s04 s) indices04 values04 4672 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=4672#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠15#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨32#u32,JGm_TX2_View.index (s04 s) indices04 values04 4672 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s04 s).«at» 4704#usize)=ok (encodeState (JGc_TX2_HashBytes.state [222,183,124,211,163,44,129,50,210,200,8,43,44,53,37,161,107,120,175,184,161,143,43,8,208,74,107,208,67,251,215,209])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 146
      5216#usize 4672#usize 4704#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings12.k1c146_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes1 4#usize 4#usize 5#usize 4704#usize 544#usize
    15#u32 (encodeState value148) (encodeState (JGc_TX2_HashBytes.state [222,183,124,211,163,44,129,50,210,200,8,43,44,53,37,161,107,120,175,184,161,143,43,8,208,74,107,208,67,251,215,209])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read04
  simp only [show 15#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls1.source159 D hash (s04 s) 5#usize 4704#usize 15#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 4704 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 4672 v04
      15#u32 4#usize (encodeState value159) 4704#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 32#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 4704 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value149) :=
    JGm_TX2_View.value (s05 s) indices05 values05 4704 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=4704#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠32#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨36#u32,JGm_TX2_View.index (s05 s) indices05 values05 4704 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s05 s).«at» 4736#usize)=ok (encodeState (JGc_TX2_HashBytes.state [254,189,31,81,29,208,193,233,179,91,165,212,189,33,236,89,123,93,223,227,10,198,30,75,72,135,26,14,69,64,45,249])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 147
      5216#usize 4704#usize 4736#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings12.k1c147_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes1 5#usize 5#usize 6#usize 4736#usize 512#usize
    32#u32 (encodeState value149) (encodeState (JGc_TX2_HashBytes.state [254,189,31,81,29,208,193,233,179,91,165,212,189,33,236,89,123,93,223,227,10,198,30,75,72,135,26,14,69,64,45,249])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read05
  simp only [show 32#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls1.source160 D hash (s05 s) 6#usize 4736#usize 32#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 4736 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 4704 v05
      32#u32 5#usize (encodeState value160) 4736#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 36#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 4736 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value150) :=
    JGm_TX2_View.value (s06 s) indices06 values06 4736 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=4736#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠36#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨40#u32,JGm_TX2_View.index (s06 s) indices06 values06 4736 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s06 s).«at» 4768#usize)=ok (encodeState (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 148
      5216#usize 4736#usize 4768#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings12.k1c148_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes1 6#usize 6#usize 7#usize 4768#usize 480#usize
    36#u32 (encodeState value150) (encodeState (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read06
  simp only [show 36#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls1.source161 D hash (s06 s) 7#usize 4768#usize 36#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 4768 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 4736 v06
      36#u32 6#usize (encodeState value161) 4768#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 40#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 4768 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value151) :=
    JGm_TX2_View.value (s07 s) indices07 values07 4768 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=4768#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠40#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨43#u32,JGm_TX2_View.index (s07 s) indices07 values07 4768 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s07 s).«at» 4800#usize)=ok (encodeState (JGc_TX2_HashBytes.state [148,185,120,73,129,121,117,223,246,81,133,240,79,138,206,51,127,230,60,221,213,155,35,140,62,115,215,223,145,85,229,14])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 149
      5216#usize 4768#usize 4800#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings12.k1c149_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes1 7#usize 7#usize 8#usize 4800#usize 448#usize
    40#u32 (encodeState value151) (encodeState (JGc_TX2_HashBytes.state [148,185,120,73,129,121,117,223,246,81,133,240,79,138,206,51,127,230,60,221,213,155,35,140,62,115,215,223,145,85,229,14])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read07
  simp only [show 40#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls1.source162 D hash (s07 s) 8#usize 4800#usize 40#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 4800 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 4768 v07
      40#u32 7#usize (encodeState value162) 4800#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 43#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 4800 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value152) :=
    JGm_TX2_View.value (s08 s) indices08 values08 4800 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=4800#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠43#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨45#u32,JGm_TX2_View.index (s08 s) indices08 values08 4800 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s08 s).«at» 4832#usize)=ok (encodeState (JGc_TX2_HashBytes.state [82,44,102,52,93,97,36,97,250,159,210,80,233,1,56,234,81,171,0,214,205,101,168,12,128,47,171,190,96,28,134,18])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 150
      5216#usize 4800#usize 4832#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings12.k1c150_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes1 8#usize 8#usize 9#usize 4832#usize 416#usize
    43#u32 (encodeState value152) (encodeState (JGc_TX2_HashBytes.state [82,44,102,52,93,97,36,97,250,159,210,80,233,1,56,234,81,171,0,214,205,101,168,12,128,47,171,190,96,28,134,18])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read08
  simp only [show 43#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls1.source163 D hash (s08 s) 9#usize 4832#usize 43#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 4832 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 4800 v08
      43#u32 8#usize (encodeState value163) 4832#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 45#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 4832 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value153) :=
    JGm_TX2_View.value (s09 s) indices09 values09 4832 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=4832#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠45#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨53#u32,JGm_TX2_View.index (s09 s) indices09 values09 4832 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s09 s).«at» 4864#usize)=ok (encodeState (JGc_TX2_HashBytes.state [54,157,250,112,154,175,37,244,121,98,202,70,16,157,20,193,216,197,16,217,246,49,23,128,81,70,252,84,93,154,96,211])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 151
      5216#usize 4832#usize 4864#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings12.k1c151_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes1 9#usize 9#usize 10#usize 4864#usize 384#usize
    45#u32 (encodeState value153) (encodeState (JGc_TX2_HashBytes.state [54,157,250,112,154,175,37,244,121,98,202,70,16,157,20,193,216,197,16,217,246,49,23,128,81,70,252,84,93,154,96,211])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read09
  simp only [show 45#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls1.source164 D hash (s09 s) 10#usize 4864#usize 45#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 4864 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 4832 v09
      45#u32 9#usize (encodeState value164) 4864#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 53#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 4864 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value154) :=
    JGm_TX2_View.value (s10 s) indices10 values10 4864 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=4864#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠53#u32 ^^^ 1#u32 := by
    intro more
    change (11:Nat)<(s10 s).n.val at more
    rw [v10.size] at more
    exact False.elim ((by decide : ¬(11:Nat)<11) more)
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s10 s).«at» 4896#usize)=ok (encodeState (JGc_TX2_HashBytes.state [8,95,41,129,128,138,153,200,28,88,203,75,164,57,175,143,60,217,244,161,197,157,250,28,153,248,23,196,237,237,138,91])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 152
      5216#usize 4864#usize 4896#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings12.k1c152_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes1 10#usize 10#usize 11#usize 4896#usize 352#usize
    53#u32 (encodeState value154) (encodeState (JGc_TX2_HashBytes.state [8,95,41,129,128,138,153,200,28,88,203,75,164,57,175,143,60,217,244,161,197,157,250,28,153,248,23,196,237,237,138,91])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read10
  simp only [show 53#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes1 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls1.source165 D hash (s10 s) 11#usize 4896#usize 53#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 4896 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 4864 v10
      53#u32 10#usize (encodeState value165) 4896#usize (by decide)
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
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s11 s).n.val≤11;rw [v11.size];decide)
  · exact JGm_TX2_View.finish (s11 s) indices11 values11 4896
      v11 11#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level1_12
end
