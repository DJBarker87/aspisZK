import JGu_ParentCalls1
import JGm_TX2_View
import JGm_TX2_RowControl
import JGm_TX2_ExternalRun
import JGu_Supplied
import JGk_TX2_SiblingLaws
import JFw_Frames
import JFq_Range
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JGu_Level1_15
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JGr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGu_Supplied.nodes1
def indices00 : List U32 := [2#u32,4#u32,5#u32,6#u32,7#u32]
def values00 : List (Array U8 32#usize) := [encodeState value146,encodeState value147,encodeState value148,encodeState value149,encodeState value150]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s00 s) 2#u32 0#usize (encodeState value151) 4384#usize
 def indices01 : List U32 := [1#u32,4#u32,5#u32,6#u32,7#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value151,encodeState value147,encodeState value148,encodeState value149,encodeState value150]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s01 s) 4#u32 1#usize (encodeState value152) 4384#usize
 def indices02 : List U32 := [1#u32,2#u32,5#u32,6#u32,7#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value151,encodeState value152,encodeState value148,encodeState value149,encodeState value150]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_ParentWrite.after (s02 s) 6#u32 2#usize (encodeState value153) 4384#usize
 def indices03 : List U32 := [1#u32,2#u32,3#u32,6#u32,7#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value151,encodeState value152,encodeState value153,encodeState value149,encodeState value150]
def output (s : reference.Scratch) : reference.Scratch := {s03 s with n:=3#usize}
 def indicesOut : List U32 := [1#u32,2#u32,3#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value151,encodeState value152,encodeState value153]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      4352#usize 4384#usize)=ok (encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160])) := by
  unfold JGu_Supplied.nodes1
  rw [JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 4352#usize 4384#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 4352#usize 4384#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 4352).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37383).take 32)=(encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 4352#usize 4384#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160])).property];decide)
  exact same ▸ run
#print axioms read00
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 4352) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 4384 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 4352 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 2#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 4352 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value146) :=
    JGm_TX2_View.value (s00 s) indices00 values00 4352 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=4352#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠2#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨4#u32,JGm_TX2_View.index (s00 s) indices00 values00 4352 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGu_Supplied.nodes1
      (s00 s).«at» 4384#usize)=ok (encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGu_Supplied.nodes1 0#usize 0#usize 1#usize 4384#usize 64#usize
    2#u32 (encodeState value146) (encodeState (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160])) ri00 rv00
    (JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGu_Supplied.length1
        rw [len,cursor00];exact JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGu_Supplied.length1];decide) read00
  simp only [show 2#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JGu_ParentCalls1.source151 D hash (s00 s) 1#usize 4384#usize 2#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 4384 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 4352 v00
      2#u32 0#usize (encodeState value151) 4384#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 4#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 4384 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value147) :=
    JGm_TX2_View.value (s01 s) indices01 values01 4384 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=4384#usize := UScalar.eq_of_val_eq v01.at_eq
  have rn01 : Array.index_usize (s01 s).idx 2#usize=ok (4#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s01 s) indices01 values01 4384 v01 2#usize (by decide)
  have rr01 : Array.index_usize (s01 s).val 2#usize=ok (encodeState value148) :=
    JGm_TX2_View.value (s01 s) indices01 values01 4384 v01 2#usize (by decide)
  have selected01 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGu_Supplied.nodes1 1#usize 1#usize 2#usize 3#usize 4#u32
    (encodeState value147) (encodeState value148) ri01 rv01
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (2:Nat)<(s01 s).n.val;rw [v01.size];decide)
    rn01 rr01 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 3#usize 2#usize) := by
    rw [selected01]
    rw [cursor01]
    exact JGu_ParentCalls1.source152 D hash (s01 s) 3#usize 4384#usize 4#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 4384 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 4384 v01
      4#u32 1#usize (encodeState value152) 4384#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 3#usize=ok 6#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 4384 v02 3#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 3#usize=ok (encodeState value149) :=
    JGm_TX2_View.value (s02 s) indices02 values02 4384 v02 3#usize (by decide)
  have active02 : 3#usize<(s02 s).n := by
    change (3:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=4384#usize := UScalar.eq_of_val_eq v02.at_eq
  have rn02 : Array.index_usize (s02 s).idx 4#usize=ok (6#u32 ^^^ 1#u32) :=
    JGm_TX2_View.index (s02 s) indices02 values02 4384 v02 4#usize (by decide)
  have rr02 : Array.index_usize (s02 s).val 4#usize=ok (encodeState value150) :=
    JGm_TX2_View.value (s02 s) indices02 values02 4384 v02 4#usize (by decide)
  have selected02 := JGm_TX2_BinarySelect.pair
    (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGu_Supplied.nodes1 3#usize 2#usize 4#usize 5#usize 6#u32
    (encodeState value149) (encodeState value150) ri02 rv02
    (JGm_TX2_Scalar.add _ _ _ rfl)
    (by change (4:Nat)<(s02 s).n.val;rw [v02.size];decide)
    rn02 rr02 (JGm_TX2_Scalar.add _ _ _ rfl)
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGu_Supplied.nodes1 3#usize 2#usize=
        ok (.Next (s03 s) 5#usize 3#usize) := by
    rw [selected02]
    rw [cursor02]
    exact JGu_ParentCalls1.source153 D hash (s02 s) 5#usize 4384#usize 6#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 4384 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 4384 v02
      6#u32 2#usize (encodeState value153) 4384#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGu_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGu_Supplied.nodes1 1#usize 1#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGu_Supplied.nodes1 3#usize 2#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGu_Supplied.nodes1 5#usize 3#usize :=
        JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = ok (.Done (output s)) := JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s03 s).n.val≤5;rw [v03.size];decide)
  · exact JGm_TX2_View.finish (s03 s) indices03 values03 4384
      v03 3#usize (by decide)
#print axioms source
end AspisR1.JGu_Level1_15
end
