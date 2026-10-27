import JGu_Levels0
import JGu_PaddingScan
import JGr_Counts
import Port4B_Bounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_Terminal0
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGp_Slot0.value

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGr_M0Root.retainedRoot) 0#usize hash
      0#usize 10#usize 0#usize (JGu_Keys.keys 0)
      (JGu_Scratch0.s10 s).idx (JGu_Scratch0.s10 s).val 10#usize 10#usize=
        ok (.done ((JGu_Verify0.output D hash s).idx,(JGu_Verify0.output D hash s).val,some (.Ok ()))) := by
  have frontRead : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      (JGu_Scratch0.s10 s).idx {«end»:=10#usize}=ok JGr_Count0.frontier := by
    simp only [Array.index_SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index]
    rw [if_pos (by change (10:Nat)≤(JGu_Scratch0.s10 s).idx.val.length;rw [(JGu_Scratch0.s10 s).idx.property];decide)]
    apply congrArg ok
    apply Subtype.ext
    exact JGu_Initial0.idx10 s
  have mul : Usize.wrapping_mul 32#usize 138#usize=4416#usize := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_mul_val_eq]
    apply Nat.mod_eq_of_lt
    rw [UScalar.size_def]
    scalar_tac
  have fits : (4416#usize).val≤JGp_Slot0.value.val.length := by
    have len : JGp_Slot0.value.val.length=4672 := JGp_Slot0.length
    rw [len]
    decide
  have drop : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      JGp_Slot0.value {start:=4416#usize}=ok JGu_Padding0.padding :=
    MultiproofConeSlices.drop_total _ _ fits
  have prefixRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      JGp_Slot0.value {«end»:=4416#usize}=ok JGu_Supplied.nodes0 :=
    MultiproofConeSlices.prefix_total _ _ fits
  obtain ⟨ce,after,chunks,scan⟩ := JGu_PaddingScan.calls (JGc_TX2_RealLeaves.dictionary D)
    JGu_Padding0.padding JGu_Padding0.bytes
  simp only [Port3_BatchStd.install] at scan
  have verify : Port4B_Install.leaves.op10 (JGc_TX2_RealLeaves.dictionary D) hash .Two
      (encodeState JGr_M0Root.retainedRoot)
      (JGu_Scratch0.s10 s).idx (JGu_Scratch0.s10 s).val 10#usize JGu_Supplied.nodes0=
      ok (true,(JGu_Verify0.output D hash s).idx,(JGu_Verify0.output D hash s).val) := by
    change (do
      let (b,out) ← reference.verify_owned
        (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
        (encodeState JGr_M0Root.retainedRoot) (JGu_Scratch0.s10 s) JGu_Supplied.nodes0
      ok (b,out.idx,out.val))=_
    rw [JGu_Verify0.source D hash s]
    rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body,
    if_neg (by decide : ¬10#usize<10#usize),frontRead]
  have countRead := JGr_Count0.source
  have nodeRead := JGp_Slot0.source
  change Port4B_Install.leaves.op11 .Two _=_ at countRead
  simp only [bind_tc_ok,Port3_BatchStd.install,countRead,Port3_BatchStd.okOr,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [nodeRead]
  simp only [bind_tc_ok]
  have capacity : Array.index_usize
      (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize])
      0#usize=ok 146#usize := rfl
  rw [capacity]
  simp only [bind_tc_ok,show ¬138#usize>146#usize from by decide,if_false,
    mul,lift,drop,chunks,scan,prefixRead,verify,Bool.false_eq_true,Bool.true_eq,if_true]
  all_goals rfl
#print axioms source

theorem loop {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGr_M0Root.retainedRoot) 0#usize
      (JGu_Scratch0.s00 s).idx (JGu_Scratch0.s00 s).val hash 0#usize 10#usize 0#usize
      (JGu_Keys.keys 0) 0#usize 0#usize=
        ok ((JGu_Verify0.output D hash s).idx,(JGu_Verify0.output D hash s).val,some (.Ok ())) := by
  apply (JGu_Scratch0.source D hash (encodeState JGr_M0Root.retainedRoot) s).trans
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGr_M0Root.retainedRoot) 0#usize
      (JGu_Scratch0.s10 s).idx (JGu_Scratch0.s10 s).val hash 0#usize 10#usize 0#usize
      (JGu_Keys.keys 0) 10#usize 10#usize=_
  conv_lhs =>
    unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
    rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,source,bind_tc_ok]
#print axioms loop

theorem tree {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState JGr_M0Root.retainedRoot)
      0#usize 0#usize s.idx s.val hash=
        ok (.Ok (), (JGu_Verify0.output D hash s).idx,(JGu_Verify0.output D hash s).val) := by
  have splitCount : Usize.wrapping_sub 10#usize 0#usize=10#usize := rfl
  have slot : Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) 0#usize=0#usize := rfl
  have hi : (Port3_BatchStd.install Port4B_Install.leaves).op13=ok 10#usize := rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree,if_pos rfl]
  simp only [hi,bind_tc_ok,lift,splitCount,slot]
  have build : (Port3_BatchStd.install Port4B_Install.leaves).op4 JFo_Prepared.value.queries
      0#usize 10#usize 0#usize=ok (JGr_Keys.raw 0) := JGr_Keys.build 0#usize (by decide)
  have sort : (Port3_BatchStd.install Port4B_Install.leaves).op5 (JGr_Keys.raw 0) 10#usize=
      ok (JGu_Keys.keys 0) := JGu_Keys.returned 0
  rw [build,bind_tc_ok,sort,bind_tc_ok]
  have run := loop D hash s
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGr_M0Root.retainedRoot) 0#usize
      s.idx s.val hash 0#usize 10#usize 0#usize (JGu_Keys.keys 0) 0#usize 0#usize=_ at run
  rw [run]
  rfl
#print axioms tree
end AspisR1.JGu_Terminal0
end
