import NDO_JGm_TX2_ParentCalls1
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level1_13
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGh_TX2_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes1
def indices00 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32,16#u32,18#u32,20#u32,21#u32,22#u32,26#u32]
def values00 : List (Array U8 32#usize) := [encodeState value155,encodeState value156,encodeState value157,encodeState value158,encodeState value159,encodeState value160,encodeState value161,encodeState value162,encodeState value163,encodeState value164,encodeState value165]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 1#u32 0#usize (encodeState value166) 4928#usize
 def indices01 : List U32 := [0#u32,2#u32,5#u32,6#u32,7#u32,16#u32,18#u32,20#u32,21#u32,22#u32,26#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value166,encodeState value156,encodeState value157,encodeState value158,encodeState value159,encodeState value160,encodeState value161,encodeState value162,encodeState value163,encodeState value164,encodeState value165]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 2#u32 1#usize (encodeState value167) 4960#usize
 def indices02 : List U32 := [0#u32,1#u32,5#u32,6#u32,7#u32,16#u32,18#u32,20#u32,21#u32,22#u32,26#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value166,encodeState value167,encodeState value157,encodeState value158,encodeState value159,encodeState value160,encodeState value161,encodeState value162,encodeState value163,encodeState value164,encodeState value165]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 5#u32 2#usize (encodeState value168) 4992#usize
 def indices03 : List U32 := [0#u32,1#u32,2#u32,6#u32,7#u32,16#u32,18#u32,20#u32,21#u32,22#u32,26#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value166,encodeState value167,encodeState value168,encodeState value158,encodeState value159,encodeState value160,encodeState value161,encodeState value162,encodeState value163,encodeState value164,encodeState value165]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 6#u32 3#usize (encodeState value169) 4992#usize
 def indices04 : List U32 := [0#u32,1#u32,2#u32,3#u32,7#u32,16#u32,18#u32,20#u32,21#u32,22#u32,26#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value166,encodeState value167,encodeState value168,encodeState value169,encodeState value159,encodeState value160,encodeState value161,encodeState value162,encodeState value163,encodeState value164,encodeState value165]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 16#u32 4#usize (encodeState value170) 5024#usize
 def indices05 : List U32 := [0#u32,1#u32,2#u32,3#u32,8#u32,16#u32,18#u32,20#u32,21#u32,22#u32,26#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value166,encodeState value167,encodeState value168,encodeState value169,encodeState value170,encodeState value160,encodeState value161,encodeState value162,encodeState value163,encodeState value164,encodeState value165]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 18#u32 5#usize (encodeState value171) 5056#usize
 def indices06 : List U32 := [0#u32,1#u32,2#u32,3#u32,8#u32,9#u32,18#u32,20#u32,21#u32,22#u32,26#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value166,encodeState value167,encodeState value168,encodeState value169,encodeState value170,encodeState value171,encodeState value161,encodeState value162,encodeState value163,encodeState value164,encodeState value165]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 20#u32 6#usize (encodeState value172) 5056#usize
 def indices07 : List U32 := [0#u32,1#u32,2#u32,3#u32,8#u32,9#u32,10#u32,20#u32,21#u32,22#u32,26#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value166,encodeState value167,encodeState value168,encodeState value169,encodeState value170,encodeState value171,encodeState value172,encodeState value162,encodeState value163,encodeState value164,encodeState value165]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 22#u32 7#usize (encodeState value173) 5088#usize
 def indices08 : List U32 := [0#u32,1#u32,2#u32,3#u32,8#u32,9#u32,10#u32,11#u32,21#u32,22#u32,26#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value166,encodeState value167,encodeState value168,encodeState value169,encodeState value170,encodeState value171,encodeState value172,encodeState value173,encodeState value163,encodeState value164,encodeState value165]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 26#u32 8#usize (encodeState value174) 5120#usize
 def indices09 : List U32 := [0#u32,1#u32,2#u32,3#u32,8#u32,9#u32,10#u32,11#u32,13#u32,22#u32,26#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value166,encodeState value167,encodeState value168,encodeState value169,encodeState value170,encodeState value171,encodeState value172,encodeState value173,encodeState value174,encodeState value164,encodeState value165]
def output (s : reference.Scratch) : reference.Scratch := {s09 s with n:=9#usize}
 def indicesOut : List U32 := [0#u32,1#u32,2#u32,3#u32,8#u32,9#u32,10#u32,11#u32,13#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value166,encodeState value167,encodeState value168,encodeState value169,encodeState value170,encodeState value171,encodeState value172,encodeState value173,encodeState value174]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 4896) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 5120 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 4896 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 1#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 4896 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value155) :=
    JGm_TX2_View.value (s00 s) indices00 values00 4896 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=4896#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠1#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨2#u32,JGm_TX2_View.index (s00 s) indices00 values00 4896 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s00 s).«at» 4928#usize)=ok (encodeState (JGc_TX2_HashBytes.state [83,203,141,47,29,49,83,0,229,119,249,157,202,75,8,137,134,86,89,187,41,192,74,79,178,93,121,27,76,166,10,122])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 153
      5216#usize 4896#usize 4928#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings13.k1c153_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes1 0#usize 0#usize 1#usize 4928#usize 320#usize
    1#u32 (encodeState value155) (encodeState (JGc_TX2_HashBytes.state [83,203,141,47,29,49,83,0,229,119,249,157,202,75,8,137,134,86,89,187,41,192,74,79,178,93,121,27,76,166,10,122])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read00
  simp only [show 1#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls1.source166 D hash (s00 s) 1#usize 4928#usize 1#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 4928 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 4896 v00
      1#u32 0#usize (encodeState value166) 4928#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 2#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 4928 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value156) :=
    JGm_TX2_View.value (s01 s) indices01 values01 4928 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=4928#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠2#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨5#u32,JGm_TX2_View.index (s01 s) indices01 values01 4928 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s01 s).«at» 4960#usize)=ok (encodeState (JGc_TX2_HashBytes.state [196,221,2,183,23,248,133,73,8,51,42,147,161,96,75,209,207,56,209,208,20,232,101,7,108,174,79,78,94,219,127,125])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 154
      5216#usize 4928#usize 4960#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings13.k1c154_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes1 1#usize 1#usize 2#usize 4960#usize 288#usize
    2#u32 (encodeState value156) (encodeState (JGc_TX2_HashBytes.state [196,221,2,183,23,248,133,73,8,51,42,147,161,96,75,209,207,56,209,208,20,232,101,7,108,174,79,78,94,219,127,125])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read01
  simp only [show 2#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls1.source167 D hash (s01 s) 2#usize 4960#usize 2#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 4960 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 4928 v01
      2#u32 1#usize (encodeState value167) 4960#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 5#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 4960 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value157) :=
    JGm_TX2_View.value (s02 s) indices02 values02 4960 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=4960#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠5#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨6#u32,JGm_TX2_View.index (s02 s) indices02 values02 4960 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s02 s).«at» 4992#usize)=ok (encodeState (JGc_TX2_HashBytes.state [210,139,140,59,153,186,251,0,172,145,80,161,74,249,119,170,61,196,198,137,184,185,136,105,74,136,176,56,243,80,148,155])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 155
      5216#usize 4960#usize 4992#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings13.k1c155_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes1 2#usize 2#usize 3#usize 4992#usize 256#usize
    5#u32 (encodeState value157) (encodeState (JGc_TX2_HashBytes.state [210,139,140,59,153,186,251,0,172,145,80,161,74,249,119,170,61,196,198,137,184,185,136,105,74,136,176,56,243,80,148,155])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read02
  simp only [show 5#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls1.source168 D hash (s02 s) 3#usize 4992#usize 5#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 4992 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 4960 v02
      5#u32 2#usize (encodeState value168) 4992#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 6#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 4992 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value158) :=
    JGm_TX2_View.value (s03 s) indices03 values03 4992 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=4992#usize := UScalar.eq_of_val_eq v03.at_eq
  have rn03 : Array.index_usize (s03 s).idx 4#usize=ok (6#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s03 s) indices03 values03 4992 v03 4#usize (by decide)
  have rr03 : Array.index_usize (s03 s).val 4#usize=ok (encodeState value159) :=
    JGm_TX2_View.value (s03 s) indices03 values03 4992 v03 4#usize (by decide)
  have selected03 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes1 3#usize 3#usize 4#usize 5#usize 6#u32
    (encodeState value158) (encodeState value159) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (4:Nat)<(s03 s).n.val;rw [v03.size];decide)
    rn03 rr03 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 5#usize 4#usize) := by
    rw [selected03]
    rw [cursor03]
    exact JGm_TX2_ParentCalls1.source169 D hash (s03 s) 5#usize 4992#usize 6#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 4992 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 4992 v03
      6#u32 3#usize (encodeState value169) 4992#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 5#usize=ok 16#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 4992 v04 5#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 5#usize=ok (encodeState value160) :=
    JGm_TX2_View.value (s04 s) indices04 values04 4992 v04 5#usize (by decide)
  have active04 : 5#usize<(s04 s).n := by
    change (5:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=4992#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 6#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 6#usize=ok other ∧ other≠16#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨18#u32,JGm_TX2_View.index (s04 s) indices04 values04 4992 v04 6#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s04 s).«at» 5024#usize)=ok (encodeState (JGc_TX2_HashBytes.state [6,127,182,246,61,243,32,244,27,158,168,158,29,234,144,165,109,106,190,43,248,29,25,250,131,155,171,164,222,234,139,173])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 156
      5216#usize 4992#usize 5024#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings13.k1c156_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes1 5#usize 4#usize 6#usize 5024#usize 224#usize
    16#u32 (encodeState value160) (encodeState (JGc_TX2_HashBytes.state [6,127,182,246,61,243,32,244,27,158,168,158,29,234,144,165,109,106,190,43,248,29,25,250,131,155,171,164,222,234,139,173])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read04
  simp only [show 16#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes1 5#usize 4#usize=
        ok (.Next (s05 s) 6#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls1.source170 D hash (s04 s) 6#usize 5024#usize 16#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 5024 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 4992 v04
      16#u32 4#usize (encodeState value170) 5024#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 6#usize=ok 18#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 5024 v05 6#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 6#usize=ok (encodeState value161) :=
    JGm_TX2_View.value (s05 s) indices05 values05 5024 v05 6#usize (by decide)
  have active05 : 6#usize<(s05 s).n := by
    change (6:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=5024#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 7#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 7#usize=ok other ∧ other≠18#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨20#u32,JGm_TX2_View.index (s05 s) indices05 values05 5024 v05 7#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s05 s).«at» 5056#usize)=ok (encodeState (JGc_TX2_HashBytes.state [117,86,123,7,186,122,67,234,65,160,231,60,37,157,151,54,110,85,27,160,149,14,29,168,187,145,252,114,94,219,94,177])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 157
      5216#usize 5024#usize 5056#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings13.k1c157_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes1 6#usize 5#usize 7#usize 5056#usize 192#usize
    18#u32 (encodeState value161) (encodeState (JGc_TX2_HashBytes.state [117,86,123,7,186,122,67,234,65,160,231,60,37,157,151,54,110,85,27,160,149,14,29,168,187,145,252,114,94,219,94,177])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read05
  simp only [show 18#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes1 6#usize 5#usize=
        ok (.Next (s06 s) 7#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls1.source171 D hash (s05 s) 7#usize 5056#usize 18#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 5056 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 5024 v05
      18#u32 5#usize (encodeState value171) 5056#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 7#usize=ok 20#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 5056 v06 7#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 7#usize=ok (encodeState value162) :=
    JGm_TX2_View.value (s06 s) indices06 values06 5056 v06 7#usize (by decide)
  have active06 : 7#usize<(s06 s).n := by
    change (7:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=5056#usize := UScalar.eq_of_val_eq v06.at_eq
  have rn06 : Array.index_usize (s06 s).idx 8#usize=ok (20#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s06 s) indices06 values06 5056 v06 8#usize (by decide)
  have rr06 : Array.index_usize (s06 s).val 8#usize=ok (encodeState value163) :=
    JGm_TX2_View.value (s06 s) indices06 values06 5056 v06 8#usize (by decide)
  have selected06 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes1 7#usize 6#usize 8#usize 9#usize 20#u32
    (encodeState value162) (encodeState value163) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (8:Nat)<(s06 s).n.val;rw [v06.size];decide)
    rn06 rr06 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes1 7#usize 6#usize=
        ok (.Next (s07 s) 9#usize 7#usize) := by
    rw [selected06]
    rw [cursor06]
    exact JGm_TX2_ParentCalls1.source172 D hash (s06 s) 9#usize 5056#usize 20#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 5056 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 5056 v06
      20#u32 6#usize (encodeState value172) 5056#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 9#usize=ok 22#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 5056 v07 9#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 9#usize=ok (encodeState value164) :=
    JGm_TX2_View.value (s07 s) indices07 values07 5056 v07 9#usize (by decide)
  have active07 : 9#usize<(s07 s).n := by
    change (9:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=5056#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 10#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 10#usize=ok other ∧ other≠22#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨26#u32,JGm_TX2_View.index (s07 s) indices07 values07 5056 v07 10#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s07 s).«at» 5088#usize)=ok (encodeState (JGc_TX2_HashBytes.state [78,12,25,15,184,19,27,72,56,190,63,8,79,60,29,195,83,19,70,161,110,125,134,153,240,82,199,75,98,153,166,251])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 158
      5216#usize 5056#usize 5088#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings13.k1c158_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes1 9#usize 7#usize 10#usize 5088#usize 160#usize
    22#u32 (encodeState value164) (encodeState (JGc_TX2_HashBytes.state [78,12,25,15,184,19,27,72,56,190,63,8,79,60,29,195,83,19,70,161,110,125,134,153,240,82,199,75,98,153,166,251])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read07
  simp only [show 22#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes1 9#usize 7#usize=
        ok (.Next (s08 s) 10#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls1.source173 D hash (s07 s) 10#usize 5088#usize 22#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 5088 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 5056 v07
      22#u32 7#usize (encodeState value173) 5088#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 10#usize=ok 26#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 5088 v08 10#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 10#usize=ok (encodeState value165) :=
    JGm_TX2_View.value (s08 s) indices08 values08 5088 v08 10#usize (by decide)
  have active08 : 10#usize<(s08 s).n := by
    change (10:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=5088#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 11#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 11#usize=ok other ∧ other≠26#u32 ^^^ 1#u32 := by
    intro more
    change (11:Nat)<(s08 s).n.val at more
    rw [v08.size] at more
    exact False.elim ((by decide : ¬(11:Nat)<11) more)
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s08 s).«at» 5120#usize)=ok (encodeState (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 159
      5216#usize 5088#usize 5120#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings13.k1c159_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes1 10#usize 8#usize 11#usize 5120#usize 128#usize
    26#u32 (encodeState value165) (encodeState (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read08
  simp only [show 26#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes1 10#usize 8#usize=
        ok (.Next (s09 s) 11#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls1.source174 D hash (s08 s) 11#usize 5120#usize 26#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 5120 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 5088 v08
      26#u32 8#usize (encodeState value174) 5120#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGm_TX2_Supplied.nodes1 1#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGm_TX2_Supplied.nodes1 2#usize 2#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGm_TX2_Supplied.nodes1 3#usize 3#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGm_TX2_Supplied.nodes1 5#usize 4#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGm_TX2_Supplied.nodes1 6#usize 5#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGm_TX2_Supplied.nodes1 7#usize 6#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGm_TX2_Supplied.nodes1 9#usize 7#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGm_TX2_Supplied.nodes1 10#usize 8#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGm_TX2_Supplied.nodes1 11#usize 9#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s09 s).n.val≤11;rw [v09.size];decide)
  · exact JGm_TX2_View.finish (s09 s) indices09 values09 5120
      v09 9#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level1_13
end
