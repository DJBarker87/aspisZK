import NDO_JGm_TX2_ParentCalls0
import NDO_JGm_TX2_View
import NDO_JGm_TX2_RowControl
import NDO_JGm_TX2_ExternalRun
import NDO_JGm_TX2_Supplied
import NDO_JGk_TX2_SiblingLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Level0_00
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGf_TX2_M0Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes0
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
      s JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done (output s)) ∧
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
  have read00 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s00 s).«at» 32#usize)=ok (encodeState (JGc_TX2_HashBytes.state [189,248,141,229,232,239,254,233,229,242,34,143,253,180,238,215,115,247,158,182,28,222,73,110,160,168,132,92,222,91,14,30])) := by
    rw [cursor00]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 0
      5216#usize 0#usize 32#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings00.k0c000_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGm_TX2_Supplied.nodes0 0#usize 0#usize 1#usize 32#usize 5216#usize
    14297#u32 (encodeState value011) (encodeState (JGc_TX2_HashBytes.state [189,248,141,229,232,239,254,233,229,242,34,143,253,180,238,215,115,247,158,182,28,222,73,110,160,168,132,92,222,91,14,30])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read00
  simp only [show 14297#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGm_TX2_Supplied.nodes0 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGm_TX2_ParentCalls0.source012 D hash (s00 s) 1#usize 32#usize 14297#u32 0#usize (by decide)
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
  have read01 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s01 s).«at» 64#usize)=ok (encodeState (JGc_TX2_HashBytes.state [121,251,34,151,204,248,189,232,20,144,172,120,239,171,47,41,7,192,54,227,25,167,11,30,34,111,33,147,122,105,95,91])) := by
    rw [cursor01]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 1
      5216#usize 32#usize 64#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings00.k0c001_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected01 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGm_TX2_Supplied.nodes0 1#usize 1#usize 2#usize 64#usize 5184#usize
    21248#u32 (encodeState value007) (encodeState (JGc_TX2_HashBytes.state [121,251,34,151,204,248,189,232,20,144,172,120,239,171,47,41,7,192,54,227,25,167,11,30,34,111,33,147,122,105,95,91])) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor01];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read01
  simp only [show 21248#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGm_TX2_Supplied.nodes0 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JGm_TX2_ParentCalls0.source013 D hash (s01 s) 2#usize 64#usize 21248#u32 1#usize (by decide)
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
  have read02 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s02 s).«at» 96#usize)=ok (encodeState (JGc_TX2_HashBytes.state [226,24,141,171,213,169,205,223,209,245,68,62,123,75,40,22,136,93,163,56,171,160,93,15,187,179,86,223,148,88,54,255])) := by
    rw [cursor02]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 2
      5216#usize 64#usize 96#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings00.k0c002_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected02 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGm_TX2_Supplied.nodes0 2#usize 2#usize 3#usize 96#usize 5152#usize
    42158#u32 (encodeState value005) (encodeState (JGc_TX2_HashBytes.state [226,24,141,171,213,169,205,223,209,245,68,62,123,75,40,22,136,93,163,56,171,160,93,15,187,179,86,223,148,88,54,255])) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor02];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read02
  simp only [show 42158#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGm_TX2_Supplied.nodes0 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JGm_TX2_ParentCalls0.source014 D hash (s02 s) 3#usize 96#usize 42158#u32 2#usize (by decide)
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
  have read03 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s03 s).«at» 128#usize)=ok (encodeState (JGc_TX2_HashBytes.state [66,118,36,1,40,42,222,116,108,188,8,180,209,56,15,104,188,119,85,230,118,209,32,11,106,203,92,163,143,74,233,8])) := by
    rw [cursor03]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 3
      5216#usize 96#usize 128#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings00.k0c003_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected03 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGm_TX2_Supplied.nodes0 3#usize 3#usize 4#usize 128#usize 5120#usize
    55377#u32 (encodeState value009) (encodeState (JGc_TX2_HashBytes.state [66,118,36,1,40,42,222,116,108,188,8,180,209,56,15,104,188,119,85,230,118,209,32,11,106,203,92,163,143,74,233,8])) ri03 rv03
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor03];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read03
  simp only [show 55377#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGm_TX2_Supplied.nodes0 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JGm_TX2_ParentCalls0.source015 D hash (s03 s) 4#usize 128#usize 55377#u32 3#usize (by decide)
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
  have read04 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s04 s).«at» 160#usize)=ok (encodeState (JGc_TX2_HashBytes.state [148,155,24,4,233,10,134,242,4,94,86,3,55,144,143,64,21,197,244,8,32,203,169,93,43,249,244,77,12,22,48,232])) := by
    rw [cursor04]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 4
      5216#usize 128#usize 160#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings00.k0c004_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected04 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGm_TX2_Supplied.nodes0 4#usize 4#usize 5#usize 160#usize 5088#usize
    63860#u32 (encodeState value008) (encodeState (JGc_TX2_HashBytes.state [148,155,24,4,233,10,134,242,4,94,86,3,55,144,143,64,21,197,244,8,32,203,169,93,43,249,244,77,12,22,48,232])) ri04 rv04
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor04];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read04
  simp only [show 63860#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGm_TX2_Supplied.nodes0 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JGm_TX2_ParentCalls0.source016 D hash (s04 s) 5#usize 160#usize 63860#u32 4#usize (by decide)
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
  have read05 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s05 s).«at» 192#usize)=ok (encodeState (JGc_TX2_HashBytes.state [133,81,188,75,67,217,127,245,207,139,14,33,198,21,1,183,88,46,89,97,148,72,10,110,240,165,89,230,110,243,21,149])) := by
    rw [cursor05]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 5
      5216#usize 160#usize 192#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings00.k0c005_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected05 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGm_TX2_Supplied.nodes0 5#usize 5#usize 6#usize 192#usize 5056#usize
    132355#u32 (encodeState value000) (encodeState (JGc_TX2_HashBytes.state [133,81,188,75,67,217,127,245,207,139,14,33,198,21,1,183,88,46,89,97,148,72,10,110,240,165,89,230,110,243,21,149])) ri05 rv05
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor05];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read05
  simp only [show 132355#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGm_TX2_Supplied.nodes0 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JGm_TX2_ParentCalls0.source017 D hash (s05 s) 6#usize 192#usize 132355#u32 5#usize (by decide)
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
  have read06 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s06 s).«at» 224#usize)=ok (encodeState (JGc_TX2_HashBytes.state [154,30,211,64,221,253,33,44,222,183,203,129,137,147,202,30,36,187,246,13,210,34,93,124,10,83,51,167,148,141,26,0])) := by
    rw [cursor06]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 6
      5216#usize 192#usize 224#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings00.k0c006_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected06 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGm_TX2_Supplied.nodes0 6#usize 6#usize 7#usize 224#usize 5024#usize
    149624#u32 (encodeState value003) (encodeState (JGc_TX2_HashBytes.state [154,30,211,64,221,253,33,44,222,183,203,129,137,147,202,30,36,187,246,13,210,34,93,124,10,83,51,167,148,141,26,0])) ri06 rv06
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor06];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read06
  simp only [show 149624#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGm_TX2_Supplied.nodes0 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JGm_TX2_ParentCalls0.source018 D hash (s06 s) 7#usize 224#usize 149624#u32 6#usize (by decide)
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
  have read07 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s07 s).«at» 256#usize)=ok (encodeState (JGc_TX2_HashBytes.state [32,198,90,69,50,216,55,227,243,115,213,199,174,136,234,163,54,49,47,75,127,15,0,171,207,239,114,238,210,101,243,33])) := by
    rw [cursor07]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 7
      5216#usize 224#usize 256#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings00.k0c007_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected07 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGm_TX2_Supplied.nodes0 7#usize 7#usize 8#usize 256#usize 4992#usize
    166165#u32 (encodeState value004) (encodeState (JGc_TX2_HashBytes.state [32,198,90,69,50,216,55,227,243,115,213,199,174,136,234,163,54,49,47,75,127,15,0,171,207,239,114,238,210,101,243,33])) ri07 rv07
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor07];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read07
  simp only [show 166165#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGm_TX2_Supplied.nodes0 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JGm_TX2_ParentCalls0.source019 D hash (s07 s) 8#usize 256#usize 166165#u32 7#usize (by decide)
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
  have read08 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s08 s).«at» 288#usize)=ok (encodeState (JGc_TX2_HashBytes.state [234,103,151,200,111,92,71,73,125,108,96,37,87,158,96,155,23,104,213,245,190,48,225,244,170,117,145,136,249,7,136,43])) := by
    rw [cursor08]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 8
      5216#usize 256#usize 288#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings00.k0c008_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected08 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGm_TX2_Supplied.nodes0 8#usize 8#usize 9#usize 288#usize 4960#usize
    178080#u32 (encodeState value002) (encodeState (JGc_TX2_HashBytes.state [234,103,151,200,111,92,71,73,125,108,96,37,87,158,96,155,23,104,213,245,190,48,225,244,170,117,145,136,249,7,136,43])) ri08 rv08
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor08];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read08
  simp only [show 178080#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGm_TX2_Supplied.nodes0 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JGm_TX2_ParentCalls0.source020 D hash (s08 s) 9#usize 288#usize 178080#u32 8#usize (by decide)
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
  have read09 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s09 s).«at» 320#usize)=ok (encodeState (JGc_TX2_HashBytes.state [73,139,26,79,32,250,87,38,215,58,56,39,115,73,199,106,78,78,252,70,254,176,53,155,125,59,121,74,189,238,228,73])) := by
    rw [cursor09]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 9
      5216#usize 288#usize 320#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings00.k0c009_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected09 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGm_TX2_Supplied.nodes0 9#usize 9#usize 10#usize 320#usize 4928#usize
    179622#u32 (encodeState value006) (encodeState (JGc_TX2_HashBytes.state [73,139,26,79,32,250,87,38,215,58,56,39,115,73,199,106,78,78,252,70,254,176,53,155,125,59,121,74,189,238,228,73])) ri09 rv09
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor09];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read09
  simp only [show 179622#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGm_TX2_Supplied.nodes0 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JGm_TX2_ParentCalls0.source021 D hash (s09 s) 10#usize 320#usize 179622#u32 9#usize (by decide)
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
  have read10 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s10 s).«at» 352#usize)=ok (encodeState (JGc_TX2_HashBytes.state [219,235,44,83,194,181,197,200,108,49,49,252,53,227,196,164,245,43,179,245,187,38,84,185,232,200,232,124,197,98,125,188])) := by
    rw [cursor10]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 10
      5216#usize 320#usize 352#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings00.k0c010_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected10 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s10 s)
    JGm_TX2_Supplied.nodes0 10#usize 10#usize 11#usize 352#usize 4896#usize
    185637#u32 (encodeState value010) (encodeState (JGc_TX2_HashBytes.state [219,235,44,83,194,181,197,200,108,49,49,252,53,227,196,164,245,43,179,245,187,38,84,185,232,200,232,124,197,98,125,188])) ri10 rv10
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired10
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor10];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor10];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor10];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read10
  simp only [show 185637#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected10
  have row10 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s10 s) JGm_TX2_Supplied.nodes0 10#usize 10#usize=
        ok (.Next (s11 s) 11#usize 11#usize) := by
    rw [selected10]
    exact JGm_TX2_ParentCalls0.source022 D hash (s10 s) 11#usize 352#usize 185637#u32 10#usize (by decide)
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
  have read11 : reference.read32 (MultiproofConeSlices.sub JGm_TX2_Supplied.nodes0
      (s11 s).«at» 384#usize)=ok (encodeState (JGc_TX2_HashBytes.state [149,78,203,164,143,37,62,165,229,108,172,236,145,217,217,36,250,242,23,199,180,137,90,249,85,65,225,142,183,54,118,117])) := by
    rw [cursor11]
    have read := JGm_TX2_Supplied.source JGh_TX2_NodeViews.nodes0 11
      5216#usize 352#usize 384#usize rfl rfl (by decide)
      (by rw [JGh_TX2_NodeViews.length0];decide)
    rw [JGh_TX2_Siblings00.k0c011_read] at read
    simpa only [JGm_TX2_Supplied.nodes0,JGf_TX2_M0Roots.siblingAt] using read
  have selected11 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s11 s)
    JGm_TX2_Supplied.nodes0 11#usize 11#usize 12#usize 384#usize 4864#usize
    218094#u32 (encodeState value001) (encodeState (JGc_TX2_HashBytes.state [149,78,203,164,143,37,62,165,229,108,172,236,145,217,217,36,250,242,23,199,180,137,90,249,85,65,225,142,183,54,118,117])) ri11 rv11
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired11
    (by have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
        rw [len,cursor11];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor11];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor11];decide)
    (by rw [JGm_TX2_Supplied.length0];decide) read11
  simp only [show 218094#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected11
  have row11 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s11 s) JGm_TX2_Supplied.nodes0 11#usize 11#usize=
        ok (.Next (s12 s) 12#usize 12#usize) := by
    rw [selected11]
    exact JGm_TX2_ParentCalls0.source023 D hash (s11 s) 12#usize 384#usize 218094#u32 11#usize (by decide)
  have v12 : JGm_TX2_View.View (s12 s) indices12 values12 384 := by
    have v := JGm_TX2_View.after (s11 s) indices11 values11 352 v11
      218094#u32 11#usize (encodeState value023) 384#usize (by decide)
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
  · exact JGm_TX2_View.finish (s12 s) indices12 values12 384
      v12 12#usize (by decide)
#print axioms source
end AspisR1.JGm_TX2_Level0_00
end
