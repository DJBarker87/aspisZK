import NDO_JGm_TX2_ParentCalls1
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level1_14
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGh_TX2_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes1
def indices00 : List U32 := [0#u32,1#u32,2#u32,3#u32,8#u32,9#u32,10#u32,11#u32,13#u32]
def values00 : List (Array U8 32#usize) := [encodeState value166,encodeState value167,encodeState value168,encodeState value169,encodeState value170,encodeState value171,encodeState value172,encodeState value173,encodeState value174]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 0#u32 0#usize (encodeState value175) 5120#usize
 def indices01 : List U32 := [0#u32,1#u32,2#u32,3#u32,8#u32,9#u32,10#u32,11#u32,13#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value175,encodeState value167,encodeState value168,encodeState value169,encodeState value170,encodeState value171,encodeState value172,encodeState value173,encodeState value174]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 2#u32 1#usize (encodeState value176) 5120#usize
 def indices02 : List U32 := [0#u32,1#u32,2#u32,3#u32,8#u32,9#u32,10#u32,11#u32,13#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value175,encodeState value176,encodeState value168,encodeState value169,encodeState value170,encodeState value171,encodeState value172,encodeState value173,encodeState value174]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 8#u32 2#usize (encodeState value177) 5120#usize
 def indices03 : List U32 := [0#u32,1#u32,4#u32,3#u32,8#u32,9#u32,10#u32,11#u32,13#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value175,encodeState value176,encodeState value177,encodeState value169,encodeState value170,encodeState value171,encodeState value172,encodeState value173,encodeState value174]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 10#u32 3#usize (encodeState value178) 5120#usize
 def indices04 : List U32 := [0#u32,1#u32,4#u32,5#u32,8#u32,9#u32,10#u32,11#u32,13#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value175,encodeState value176,encodeState value177,encodeState value178,encodeState value170,encodeState value171,encodeState value172,encodeState value173,encodeState value174]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 13#u32 4#usize (encodeState value179) 5152#usize
 def indices05 : List U32 := [0#u32,1#u32,4#u32,5#u32,6#u32,9#u32,10#u32,11#u32,13#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value175,encodeState value176,encodeState value177,encodeState value178,encodeState value179,encodeState value171,encodeState value172,encodeState value173,encodeState value174]
def output (s : reference.Scratch) : reference.Scratch := {s05 s with n:=5#usize}
 def indicesOut : List U32 := [0#u32,1#u32,4#u32,5#u32,6#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value175,encodeState value176,encodeState value177,encodeState value178,encodeState value179]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 5120) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 5152 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 5120 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 5120 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value166) :=
    JGm_TX2_View.value (s00 s) indices00 values00 5120 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=5120#usize := UScalar.eq_of_val_eq v00.at_eq
  have rn00 : Array.index_usize (s00 s).idx 1#usize=ok (0#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s00 s) indices00 values00 5120 v00 1#usize (by decide)
  have rr00 : Array.index_usize (s00 s).val 1#usize=ok (encodeState value167) :=
    JGm_TX2_View.value (s00 s) indices00 values00 5120 v00 1#usize (by decide)
  have selected00 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes1 0#usize 0#usize 1#usize 2#usize 0#u32
    (encodeState value166) (encodeState value167) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (1:Nat)<(s00 s).n.val;rw [v00.size];decide)
    rn00 rr00 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 2#usize 1#usize) := by
    rw [selected00]
    rw [cursor00]
    exact JGm_TX2_ParentCalls1.source175 D hash (s00 s) 2#usize 5120#usize 0#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 5120 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 5120 v00
      0#u32 0#usize (encodeState value175) 5120#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 2#usize=ok 2#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 5120 v01 2#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 2#usize=ok (encodeState value168) :=
    JGm_TX2_View.value (s01 s) indices01 values01 5120 v01 2#usize (by decide)
  have active01 : 2#usize<(s01 s).n := by
    change (2:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=5120#usize := UScalar.eq_of_val_eq v01.at_eq
  have rn01 : Array.index_usize (s01 s).idx 3#usize=ok (2#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s01 s) indices01 values01 5120 v01 3#usize (by decide)
  have rr01 : Array.index_usize (s01 s).val 3#usize=ok (encodeState value169) :=
    JGm_TX2_View.value (s01 s) indices01 values01 5120 v01 3#usize (by decide)
  have selected01 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes1 2#usize 1#usize 3#usize 4#usize 2#u32
    (encodeState value168) (encodeState value169) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (3:Nat)<(s01 s).n.val;rw [v01.size];decide)
    rn01 rr01 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes1 2#usize 1#usize=
        ok (.Next (s02 s) 4#usize 2#usize) := by
    rw [selected01]
    rw [cursor01]
    exact JGm_TX2_ParentCalls1.source176 D hash (s01 s) 4#usize 5120#usize 2#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 5120 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 5120 v01
      2#u32 1#usize (encodeState value176) 5120#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 4#usize=ok 8#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 5120 v02 4#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 4#usize=ok (encodeState value170) :=
    JGm_TX2_View.value (s02 s) indices02 values02 5120 v02 4#usize (by decide)
  have active02 : 4#usize<(s02 s).n := by
    change (4:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=5120#usize := UScalar.eq_of_val_eq v02.at_eq
  have rn02 : Array.index_usize (s02 s).idx 5#usize=ok (8#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s02 s) indices02 values02 5120 v02 5#usize (by decide)
  have rr02 : Array.index_usize (s02 s).val 5#usize=ok (encodeState value171) :=
    JGm_TX2_View.value (s02 s) indices02 values02 5120 v02 5#usize (by decide)
  have selected02 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes1 4#usize 2#usize 5#usize 6#usize 8#u32
    (encodeState value170) (encodeState value171) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (5:Nat)<(s02 s).n.val;rw [v02.size];decide)
    rn02 rr02 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes1 4#usize 2#usize=
        ok (.Next (s03 s) 6#usize 3#usize) := by
    rw [selected02]
    rw [cursor02]
    exact JGm_TX2_ParentCalls1.source177 D hash (s02 s) 6#usize 5120#usize 8#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 5120 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 5120 v02
      8#u32 2#usize (encodeState value177) 5120#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 6#usize=ok 10#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 5120 v03 6#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 6#usize=ok (encodeState value172) :=
    JGm_TX2_View.value (s03 s) indices03 values03 5120 v03 6#usize (by decide)
  have active03 : 6#usize<(s03 s).n := by
    change (6:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=5120#usize := UScalar.eq_of_val_eq v03.at_eq
  have rn03 : Array.index_usize (s03 s).idx 7#usize=ok (10#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s03 s) indices03 values03 5120 v03 7#usize (by decide)
  have rr03 : Array.index_usize (s03 s).val 7#usize=ok (encodeState value173) :=
    JGm_TX2_View.value (s03 s) indices03 values03 5120 v03 7#usize (by decide)
  have selected03 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes1 6#usize 3#usize 7#usize 8#usize 10#u32
    (encodeState value172) (encodeState value173) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (7:Nat)<(s03 s).n.val;rw [v03.size];decide)
    rn03 rr03 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes1 6#usize 3#usize=
        ok (.Next (s04 s) 8#usize 4#usize) := by
    rw [selected03]
    rw [cursor03]
    exact JGm_TX2_ParentCalls1.source178 D hash (s03 s) 8#usize 5120#usize 10#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 5120 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 5120 v03
      10#u32 3#usize (encodeState value178) 5120#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 8#usize=ok 13#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 5120 v04 8#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 8#usize=ok (encodeState value174) :=
    JGm_TX2_View.value (s04 s) indices04 values04 5120 v04 8#usize (by decide)
  have active04 : 8#usize<(s04 s).n := by
    change (8:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=5120#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 9#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 9#usize=ok other ∧ other≠13#u32 ^^^ 1#u32 := by
    intro more
    change (9:Nat)<(s04 s).n.val at more
    rw [v04.size] at more
    exact False.elim ((by decide : ¬(9:Nat)<9) more)
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s04 s).«at» 5152#usize)=ok (encodeState (JGc_TX2_HashBytes.state [94,141,123,142,16,86,40,121,91,237,183,116,254,58,142,124,219,39,123,41,165,187,42,68,243,146,139,31,5,160,3,117])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 160
      5216#usize 5120#usize 5152#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings14.k1c160_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes1 8#usize 4#usize 9#usize 5152#usize 96#usize
    13#u32 (encodeState value174) (encodeState (JGc_TX2_HashBytes.state [94,141,123,142,16,86,40,121,91,237,183,116,254,58,142,124,219,39,123,41,165,187,42,68,243,146,139,31,5,160,3,117])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read04
  simp only [show 13#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes1 8#usize 4#usize=
        ok (.Next (s05 s) 9#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls1.source179 D hash (s04 s) 9#usize 5152#usize 13#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 5152 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 5120 v04
      13#u32 4#usize (encodeState value179) 5152#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGm_TX2_Supplied.nodes1 2#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGm_TX2_Supplied.nodes1 4#usize 2#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGm_TX2_Supplied.nodes1 6#usize 3#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGm_TX2_Supplied.nodes1 8#usize 4#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGm_TX2_Supplied.nodes1 9#usize 5#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s05 s).n.val≤9;rw [v05.size];decide)
  · exact JGm_TX2_View.finish (s05 s) indices05 values05 5152
      v05 5#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level1_14
end
