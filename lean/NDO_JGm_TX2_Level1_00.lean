import NDO_JGm_TX2_ParentCalls1
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level1_00
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGh_TX2_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes1
def indices00 : List U32 := [14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32,178080#u32,179622#u32,185637#u32,218094#u32]
def values00 : List (Array U8 32#usize) := [encodeState value011,encodeState value007,encodeState value005,encodeState value009,encodeState value008,encodeState value000,encodeState value003,encodeState value004,encodeState value002,encodeState value006,encodeState value010,encodeState value001]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 14297#u32 0#usize (encodeState value012) 32#usize
 def indices01 : List U32 := [7148#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32,178080#u32,179622#u32,185637#u32,218094#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value012,encodeState value007,encodeState value005,encodeState value009,encodeState value008,encodeState value000,encodeState value003,encodeState value004,encodeState value002,encodeState value006,encodeState value010,encodeState value001]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 21248#u32 1#usize (encodeState value013) 64#usize
 def indices02 : List U32 := [7148#u32,10624#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32,178080#u32,179622#u32,185637#u32,218094#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value012,encodeState value013,encodeState value005,encodeState value009,encodeState value008,encodeState value000,encodeState value003,encodeState value004,encodeState value002,encodeState value006,encodeState value010,encodeState value001]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 42158#u32 2#usize (encodeState value014) 96#usize
 def indices03 : List U32 := [7148#u32,10624#u32,21079#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32,178080#u32,179622#u32,185637#u32,218094#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value012,encodeState value013,encodeState value014,encodeState value009,encodeState value008,encodeState value000,encodeState value003,encodeState value004,encodeState value002,encodeState value006,encodeState value010,encodeState value001]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s03 s) 55377#u32 3#usize (encodeState value015) 128#usize
 def indices04 : List U32 := [7148#u32,10624#u32,21079#u32,27688#u32,63860#u32,132355#u32,149624#u32,166165#u32,178080#u32,179622#u32,185637#u32,218094#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value008,encodeState value000,encodeState value003,encodeState value004,encodeState value002,encodeState value006,encodeState value010,encodeState value001]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s04 s) 63860#u32 4#usize (encodeState value016) 160#usize
 def indices05 : List U32 := [7148#u32,10624#u32,21079#u32,27688#u32,31930#u32,132355#u32,149624#u32,166165#u32,178080#u32,179622#u32,185637#u32,218094#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value000,encodeState value003,encodeState value004,encodeState value002,encodeState value006,encodeState value010,encodeState value001]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s05 s) 132355#u32 5#usize (encodeState value017) 192#usize
 def indices06 : List U32 := [7148#u32,10624#u32,21079#u32,27688#u32,31930#u32,66177#u32,149624#u32,166165#u32,178080#u32,179622#u32,185637#u32,218094#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value003,encodeState value004,encodeState value002,encodeState value006,encodeState value010,encodeState value001]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s06 s) 149624#u32 6#usize (encodeState value018) 224#usize
 def indices07 : List U32 := [7148#u32,10624#u32,21079#u32,27688#u32,31930#u32,66177#u32,74812#u32,166165#u32,178080#u32,179622#u32,185637#u32,218094#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value004,encodeState value002,encodeState value006,encodeState value010,encodeState value001]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s07 s) 166165#u32 7#usize (encodeState value019) 256#usize
 def indices08 : List U32 := [7148#u32,10624#u32,21079#u32,27688#u32,31930#u32,66177#u32,74812#u32,83082#u32,178080#u32,179622#u32,185637#u32,218094#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019,encodeState value002,encodeState value006,encodeState value010,encodeState value001]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s08 s) 178080#u32 8#usize (encodeState value020) 288#usize
 def indices09 : List U32 := [7148#u32,10624#u32,21079#u32,27688#u32,31930#u32,66177#u32,74812#u32,83082#u32,89040#u32,179622#u32,185637#u32,218094#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019,encodeState value020,encodeState value006,encodeState value010,encodeState value001]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s09 s) 179622#u32 9#usize (encodeState value021) 320#usize
 def indices10 : List U32 := [7148#u32,10624#u32,21079#u32,27688#u32,31930#u32,66177#u32,74812#u32,83082#u32,89040#u32,89811#u32,185637#u32,218094#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019,encodeState value020,encodeState value021,encodeState value010,encodeState value001]
def s11 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s10 s) 185637#u32 10#usize (encodeState value022) 352#usize
 def indices11 : List U32 := [7148#u32,10624#u32,21079#u32,27688#u32,31930#u32,66177#u32,74812#u32,83082#u32,89040#u32,89811#u32,92818#u32,218094#u32]
 def values11 : List (Array U8 32#usize) := [encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019,encodeState value020,encodeState value021,encodeState value022,encodeState value001]
def s12 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s11 s) 218094#u32 11#usize (encodeState value023) 384#usize
 def indices12 : List U32 := [7148#u32,10624#u32,21079#u32,27688#u32,31930#u32,66177#u32,74812#u32,83082#u32,89040#u32,89811#u32,92818#u32,109047#u32]
 def values12 : List (Array U8 32#usize) := [encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019,encodeState value020,encodeState value021,encodeState value022,encodeState value023]
def output (s : reference.Scratch) : reference.Scratch := {s12 s with n:=12#usize}
 def indicesOut : List U32 := [7148#u32,10624#u32,21079#u32,27688#u32,31930#u32,66177#u32,74812#u32,83082#u32,89040#u32,89811#u32,92818#u32,109047#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019,encodeState value020,encodeState value021,encodeState value022,encodeState value023]
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 0) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGm_TX2_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 384 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 0 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 14297#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 0 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value011) :=
    JGm_TX2_View.value (s00 s) indices00 values00 0 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=0#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠14297#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨21248#u32,JGm_TX2_View.index (s00 s) indices00 values00 0 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s00 s).«at» 32#usize)=ok (encodeState (JGc_TX2_HashBytes.state [85,144,91,2,235,197,103,66,51,60,174,166,181,175,71,13,223,205,150,116,30,144,96,28,14,109,80,202,123,27,160,65])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 0
      5216#usize 0#usize 32#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings00.k1c000_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes1 0#usize 0#usize 1#usize 32#usize 5216#usize
    14297#u32 (encodeState value011) (encodeState (JGc_TX2_HashBytes.state [85,144,91,2,235,197,103,66,51,60,174,166,181,175,71,13,223,205,150,116,30,144,96,28,14,109,80,202,123,27,160,65])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read00
  simp only [show 14297#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls1.source012 D hash (s00 s) 1#usize 32#usize 14297#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 32 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 0 v00
      14297#u32 0#usize (encodeState value012) 32#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 21248#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 32 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value007) :=
    JGm_TX2_View.value (s01 s) indices01 values01 32 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=32#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠21248#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨42158#u32,JGm_TX2_View.index (s01 s) indices01 values01 32 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s01 s).«at» 64#usize)=ok (encodeState (JGc_TX2_HashBytes.state [149,13,90,51,150,41,51,244,252,177,230,155,168,175,140,211,78,82,178,150,84,185,68,233,36,77,141,203,84,230,147,225])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 1
      5216#usize 32#usize 64#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings00.k1c001_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes1 1#usize 1#usize 2#usize 64#usize 5184#usize
    21248#u32 (encodeState value007) (encodeState (JGc_TX2_HashBytes.state [149,13,90,51,150,41,51,244,252,177,230,155,168,175,140,211,78,82,178,150,84,185,68,233,36,77,141,203,84,230,147,225])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read01
  simp only [show 21248#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls1.source013 D hash (s01 s) 2#usize 64#usize 21248#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 64 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 32 v01
      21248#u32 1#usize (encodeState value013) 64#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 42158#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 64 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value005) :=
    JGm_TX2_View.value (s02 s) indices02 values02 64 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=64#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠42158#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨55377#u32,JGm_TX2_View.index (s02 s) indices02 values02 64 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s02 s).«at» 96#usize)=ok (encodeState (JGc_TX2_HashBytes.state [224,144,132,212,225,224,99,8,111,210,132,110,218,231,238,137,29,57,68,85,95,211,82,225,161,111,6,155,34,106,212,26])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 2
      5216#usize 64#usize 96#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings00.k1c002_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes1 2#usize 2#usize 3#usize 96#usize 5152#usize
    42158#u32 (encodeState value005) (encodeState (JGc_TX2_HashBytes.state [224,144,132,212,225,224,99,8,111,210,132,110,218,231,238,137,29,57,68,85,95,211,82,225,161,111,6,155,34,106,212,26])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read02
  simp only [show 42158#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls1.source014 D hash (s02 s) 3#usize 96#usize 42158#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 96 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 64 v02
      42158#u32 2#usize (encodeState value014) 96#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 55377#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 96 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value009) :=
    JGm_TX2_View.value (s03 s) indices03 values03 96 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=96#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠55377#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨63860#u32,JGm_TX2_View.index (s03 s) indices03 values03 96 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s03 s).«at» 128#usize)=ok (encodeState (JGc_TX2_HashBytes.state [232,117,91,224,183,62,86,67,216,228,135,232,145,180,30,213,201,219,112,52,8,112,194,249,30,166,102,198,118,58,69,125])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 3
      5216#usize 96#usize 128#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings00.k1c003_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes1 3#usize 3#usize 4#usize 128#usize 5120#usize
    55377#u32 (encodeState value009) (encodeState (JGc_TX2_HashBytes.state [232,117,91,224,183,62,86,67,216,228,135,232,145,180,30,213,201,219,112,52,8,112,194,249,30,166,102,198,118,58,69,125])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read03
  simp only [show 55377#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls1.source015 D hash (s03 s) 4#usize 128#usize 55377#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 128 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 96 v03
      55377#u32 3#usize (encodeState value015) 128#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 63860#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 128 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value008) :=
    JGm_TX2_View.value (s04 s) indices04 values04 128 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=128#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠63860#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨132355#u32,JGm_TX2_View.index (s04 s) indices04 values04 128 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s04 s).«at» 160#usize)=ok (encodeState (JGc_TX2_HashBytes.state [226,81,255,181,125,23,114,120,154,194,73,114,71,141,243,161,190,178,65,52,244,2,243,205,37,138,110,43,85,2,146,15])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 4
      5216#usize 128#usize 160#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings00.k1c004_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes1 4#usize 4#usize 5#usize 160#usize 5088#usize
    63860#u32 (encodeState value008) (encodeState (JGc_TX2_HashBytes.state [226,81,255,181,125,23,114,120,154,194,73,114,71,141,243,161,190,178,65,52,244,2,243,205,37,138,110,43,85,2,146,15])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read04
  simp only [show 63860#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls1.source016 D hash (s04 s) 5#usize 160#usize 63860#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 160 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 128 v04
      63860#u32 4#usize (encodeState value016) 160#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 132355#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 160 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value000) :=
    JGm_TX2_View.value (s05 s) indices05 values05 160 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=160#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠132355#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨149624#u32,JGm_TX2_View.index (s05 s) indices05 values05 160 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s05 s).«at» 192#usize)=ok (encodeState (JGc_TX2_HashBytes.state [232,218,175,178,220,102,209,130,17,254,196,146,81,129,213,31,99,250,20,149,224,141,2,176,15,149,167,145,180,117,156,75])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 5
      5216#usize 160#usize 192#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings00.k1c005_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes1 5#usize 5#usize 6#usize 192#usize 5056#usize
    132355#u32 (encodeState value000) (encodeState (JGc_TX2_HashBytes.state [232,218,175,178,220,102,209,130,17,254,196,146,81,129,213,31,99,250,20,149,224,141,2,176,15,149,167,145,180,117,156,75])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read05
  simp only [show 132355#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls1.source017 D hash (s05 s) 6#usize 192#usize 132355#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 192 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 160 v05
      132355#u32 5#usize (encodeState value017) 192#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 149624#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 192 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value003) :=
    JGm_TX2_View.value (s06 s) indices06 values06 192 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=192#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠149624#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨166165#u32,JGm_TX2_View.index (s06 s) indices06 values06 192 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s06 s).«at» 224#usize)=ok (encodeState (JGc_TX2_HashBytes.state [159,21,140,88,105,171,13,247,159,60,230,244,184,79,136,184,67,72,142,187,167,203,86,10,207,174,155,232,57,27,5,17])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 6
      5216#usize 192#usize 224#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings00.k1c006_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes1 6#usize 6#usize 7#usize 224#usize 5024#usize
    149624#u32 (encodeState value003) (encodeState (JGc_TX2_HashBytes.state [159,21,140,88,105,171,13,247,159,60,230,244,184,79,136,184,67,72,142,187,167,203,86,10,207,174,155,232,57,27,5,17])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read06
  simp only [show 149624#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls1.source018 D hash (s06 s) 7#usize 224#usize 149624#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 224 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 192 v06
      149624#u32 6#usize (encodeState value018) 224#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 166165#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 224 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value004) :=
    JGm_TX2_View.value (s07 s) indices07 values07 224 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=224#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠166165#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨178080#u32,JGm_TX2_View.index (s07 s) indices07 values07 224 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s07 s).«at» 256#usize)=ok (encodeState (JGc_TX2_HashBytes.state [34,186,246,47,83,202,131,21,57,208,217,199,30,181,171,77,97,75,188,20,207,46,138,240,247,156,23,222,61,35,60,214])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 7
      5216#usize 224#usize 256#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings00.k1c007_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes1 7#usize 7#usize 8#usize 256#usize 4992#usize
    166165#u32 (encodeState value004) (encodeState (JGc_TX2_HashBytes.state [34,186,246,47,83,202,131,21,57,208,217,199,30,181,171,77,97,75,188,20,207,46,138,240,247,156,23,222,61,35,60,214])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read07
  simp only [show 166165#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls1.source019 D hash (s07 s) 8#usize 256#usize 166165#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 256 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 224 v07
      166165#u32 7#usize (encodeState value019) 256#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 178080#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 256 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value002) :=
    JGm_TX2_View.value (s08 s) indices08 values08 256 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=256#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠178080#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨179622#u32,JGm_TX2_View.index (s08 s) indices08 values08 256 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s08 s).«at» 288#usize)=ok (encodeState (JGc_TX2_HashBytes.state [179,223,163,234,48,23,197,79,198,53,18,64,196,131,189,62,222,137,153,209,166,90,156,57,237,223,203,93,196,234,114,152])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 8
      5216#usize 256#usize 288#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings00.k1c008_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes1 8#usize 8#usize 9#usize 288#usize 4960#usize
    178080#u32 (encodeState value002) (encodeState (JGc_TX2_HashBytes.state [179,223,163,234,48,23,197,79,198,53,18,64,196,131,189,62,222,137,153,209,166,90,156,57,237,223,203,93,196,234,114,152])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read08
  simp only [show 178080#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls1.source020 D hash (s08 s) 9#usize 288#usize 178080#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 288 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 256 v08
      178080#u32 8#usize (encodeState value020) 288#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 179622#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 288 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value006) :=
    JGm_TX2_View.value (s09 s) indices09 values09 288 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=288#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠179622#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨185637#u32,JGm_TX2_View.index (s09 s) indices09 values09 288 v09 10#usize (by decide),by decide⟩
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s09 s).«at» 320#usize)=ok (encodeState (JGc_TX2_HashBytes.state [16,201,98,42,217,180,193,62,50,45,197,179,229,246,60,193,10,149,152,147,211,17,208,86,134,25,85,151,113,180,40,44])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 9
      5216#usize 288#usize 320#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings00.k1c009_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes1 9#usize 9#usize 10#usize 320#usize 4928#usize
    179622#u32 (encodeState value006) (encodeState (JGc_TX2_HashBytes.state [16,201,98,42,217,180,193,62,50,45,197,179,229,246,60,193,10,149,152,147,211,17,208,86,134,25,85,151,113,180,40,44])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read09
  simp only [show 179622#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls1.source021 D hash (s09 s) 10#usize 320#usize 179622#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 320 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 288 v09
      179622#u32 9#usize (encodeState value021) 320#usize (by decide)
    exact v
  have ri10 : Array.index_usize (s10 s).idx 10#usize=ok 185637#u32 :=
    JGm_TX2_View.index (s10 s) indices10 values10 320 v10 10#usize (by decide)
  have rv10 : Array.index_usize (s10 s).val 10#usize=ok (encodeState value010) :=
    JGm_TX2_View.value (s10 s) indices10 values10 320 v10 10#usize (by decide)
  have active10 : 10#usize<(s10 s).n := by
    change (10:Nat)<(s10 s).n.val
    rw [v10.size]
    decide
  have cursor10 : (s10 s).«at»=320#usize := UScalar.eq_of_val_eq v10.at_eq
  have unpaired10 : ∀ more : 11#usize<(s10 s).n,
      ∃ other,Array.index_usize (s10 s).idx 11#usize=ok other ∧ other≠185637#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨218094#u32,JGm_TX2_View.index (s10 s) indices10 values10 320 v10 11#usize (by decide),by decide⟩
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s10 s).«at» 352#usize)=ok (encodeState (JGc_TX2_HashBytes.state [96,56,13,209,41,6,60,135,83,208,126,60,234,131,233,1,255,248,5,10,214,43,67,200,182,171,54,176,54,113,174,213])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 10
      5216#usize 320#usize 352#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings00.k1c010_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes1 10#usize 10#usize 11#usize 352#usize 4896#usize
    185637#u32 (encodeState value010) (encodeState (JGc_TX2_HashBytes.state [96,56,13,209,41,6,60,135,83,208,126,60,234,131,233,1,255,248,5,10,214,43,67,200,182,171,54,176,54,113,174,213])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read10
  simp only [show 185637#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes1 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls1.source022 D hash (s10 s) 11#usize 352#usize 185637#u32 10#usize (by decide)
  have v11 : JGm_TX2_View.View (s11 s) indices11 values11 352 := by
    have v := JGm_TX2_View.after (s10 s) indices10 values10 320 v10
      185637#u32 10#usize (encodeState value022) 352#usize (by decide)
    exact v
  have ri11 : Array.index_usize (s11 s).idx 11#usize=ok 218094#u32 :=
    JGm_TX2_View.index (s11 s) indices11 values11 352 v11 11#usize (by decide)
  have rv11 : Array.index_usize (s11 s).val 11#usize=ok (encodeState value001) :=
    JGm_TX2_View.value (s11 s) indices11 values11 352 v11 11#usize (by decide)
  have active11 : 11#usize<(s11 s).n := by
    change (11:Nat)<(s11 s).n.val
    rw [v11.size]
    decide
  have cursor11 : (s11 s).«at»=352#usize := UScalar.eq_of_val_eq v11.at_eq
  have unpaired11 : ∀ more : 12#usize<(s11 s).n,
      ∃ other,Array.index_usize (s11 s).idx 12#usize=ok other ∧ other≠218094#u32 ^^^ 1#u32 := by
    intro more
    change (12:Nat)<(s11 s).n.val at more
    rw [v11.size] at more
    exact False.elim ((by decide : ¬(12:Nat)<12) more)
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes1
      (s11 s).«at» 384#usize)=ok (encodeState (JGc_TX2_HashBytes.state [28,243,229,146,24,70,89,119,248,161,25,29,238,111,230,52,67,191,127,184,7,237,245,50,78,221,13,165,220,212,138,220])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes1 11
      5216#usize 352#usize 384#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length1];decide)
    rw [JGh_TX2_Siblings00.k1c011_read] at read
    simpa only [JGm_TX2_Supplied.nodes1,JGh_TX2_M1Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes1 11#usize 11#usize 12#usize 384#usize 4864#usize
    218094#u32 (encodeState value001) (encodeState (JGc_TX2_HashBytes.state [28,243,229,146,24,70,89,119,248,161,25,29,238,111,230,52,67,191,127,184,7,237,245,50,78,221,13,165,220,212,138,220])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length1];decide) read11
  simp only [show 218094#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes1 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls1.source023 D hash (s11 s) 12#usize 384#usize 218094#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 384 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 352 v11
      218094#u32 11#usize (encodeState value023) 384#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 384
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level1_00
end
