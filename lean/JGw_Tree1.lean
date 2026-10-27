import JGw_Terminal1
import JGu_Levels1
import JGu_PaddingScan
import JGr_Counts
import Port4B_Bounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Tree1
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGp_Slot1.value

theorem tree {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState JGr_M1Root.retainedRoot)
      0#usize 1#usize s.idx s.val hash=
        ok (.Ok (), (JGu_Verify1.output D hash s).idx,(JGu_Verify1.output D hash s).val) := by
  have splitCount : Usize.wrapping_sub 10#usize 0#usize=10#usize :=
    UScalar.eq_of_val_eq (Port4B_Bounds.count 0#usize).1
  have slot : Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) 1#usize=1#usize :=
    UScalar.eq_of_val_eq (Port4B_Bounds.slot 0#usize 1#usize (by decide) (by decide))
  have hi : (Port3_BatchStd.install Port4B_Install.leaves).op13=ok 10#usize := rfl
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree
  have bounds : (if (0#usize : Usize)=0#usize then do
      let i ← (Port3_BatchStd.install Port4B_Install.leaves).op13
      ok (0#usize,i)
    else do
      let i ← (Port3_BatchStd.install Port4B_Install.leaves).op13
      ok (i,22#usize))=ok (0#usize,10#usize) := by
    rw [if_pos rfl,hi]
    rfl
  rw [bounds]
  change (do
    let a ← (Port3_BatchStd.install Port4B_Install.leaves).op4 JFo_Prepared.value.queries
      0#usize (Usize.wrapping_sub 10#usize 0#usize) 1#usize
    let keys ← (Port3_BatchStd.install Port4B_Install.leaves).op5 a (Usize.wrapping_sub 10#usize 0#usize)
    let (idx,val,pending) ← Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGr_M1Root.retainedRoot) 1#usize
      s.idx s.val hash 0#usize (Usize.wrapping_sub 10#usize 0#usize) (Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) 1#usize) keys 0#usize 0#usize
    match pending with
    | none => fail .panic
    | some r => ok (r,idx,val))=_
  rw [splitCount,slot]
  have build : (Port3_BatchStd.install Port4B_Install.leaves).op4 JFo_Prepared.value.queries
      0#usize 10#usize 1#usize=ok (JGr_Keys.raw 1) := JGr_Keys.build 1#usize (by decide)
  have sort : (Port3_BatchStd.install Port4B_Install.leaves).op5 (JGr_Keys.raw 1) 10#usize=
      ok (JGu_Keys.keys 1) := JGu_Keys.returned 1
  rw [build,bind_tc_ok,sort,bind_tc_ok]
  have run := JGw_Terminal1.loop D hash s
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGr_M1Root.retainedRoot) 1#usize
      s.idx s.val hash 0#usize 10#usize 1#usize (JGu_Keys.keys 1) 0#usize 0#usize=_ at run
  rw [run]
  rfl
#print axioms tree
end AspisR1.JGw_Tree1
end
