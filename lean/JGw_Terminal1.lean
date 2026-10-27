import JGu_Levels1
import JGu_PaddingScan
import JGr_Counts
import Port4B_Bounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Terminal1
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGp_Slot1.value

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGr_M1Root.retainedRoot) 1#usize hash
      0#usize 10#usize 1#usize (JGu_Keys.keys 1)
      (JGu_Scratch1.s10 s).idx (JGu_Scratch1.s10 s).val 10#usize 10#usize=
        ok (.done ((JGu_Verify1.output D hash s).idx,(JGu_Verify1.output D hash s).val,some (.Ok ()))) := by
  have frontRead : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      (JGu_Scratch1.s10 s).idx {«end»:=10#usize}=ok JGr_Count0.frontier := by
    simp only [Array.index_SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index]
    rw [if_pos (by change (10:Nat)≤(JGu_Scratch1.s10 s).idx.val.length;rw [(JGu_Scratch1.s10 s).idx.property];decide)]
    apply congrArg ok
    apply Subtype.ext
    exact JGu_Initial1.idx10 s
  have mul : Usize.wrapping_mul 32#usize 138#usize=4416#usize := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_mul_val_eq]
    apply Nat.mod_eq_of_lt
    rw [UScalar.size_def]
    scalar_tac
  have fits : (4416#usize).val≤JGp_Slot1.value.val.length := by
    have len : JGp_Slot1.value.val.length=4672 := JGp_Slot1.length
    rw [len]
    decide
  have drop : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      JGp_Slot1.value {start:=4416#usize}=ok JGu_Padding1.padding :=
    MultiproofConeSlices.drop_total _ _ fits
  have prefixRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      JGp_Slot1.value {«end»:=4416#usize}=ok JGu_Supplied.nodes1 :=
    MultiproofConeSlices.prefix_total _ _ fits
  obtain ⟨ce,after,chunks,scan⟩ := JGu_PaddingScan.calls (JGc_TX2_RealLeaves.dictionary D)
    JGu_Padding1.padding JGu_Padding1.bytes
  simp only [Port3_BatchStd.install] at scan
  have verify : Port4B_Install.leaves.op10 (JGc_TX2_RealLeaves.dictionary D) hash .Two
      (encodeState JGr_M1Root.retainedRoot)
      (JGu_Scratch1.s10 s).idx (JGu_Scratch1.s10 s).val 10#usize JGu_Supplied.nodes1=
      ok (true,(JGu_Verify1.output D hash s).idx,(JGu_Verify1.output D hash s).val) := by
    change (do
      let (b,out) ← reference.verify_owned
        (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
        (encodeState JGr_M1Root.retainedRoot) (JGu_Scratch1.s10 s) JGu_Supplied.nodes1
      ok (b,out.idx,out.val))=_
    rw [JGu_Verify1.source D hash s]
    rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body,
    if_neg (by decide : ¬10#usize<10#usize),frontRead]
  have countRead := JGr_Count0.source
  have nodeRead := JGp_Slot1.source
  change Port4B_Install.leaves.op3 JFx_NativeBytes.proof 1#usize=ok JGp_Slot1.value at nodeRead
  change Port4B_Install.leaves.op11 .Two _=_ at countRead
  simp only [bind_tc_ok,Port3_BatchStd.install,countRead,Port3_BatchStd.okOr,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [nodeRead]
  simp only [bind_tc_ok]
  have capacity : Array.index_usize
      (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize])
      1#usize=ok 146#usize := rfl
  rw [capacity]
  simp only [bind_tc_ok,show ¬138#usize>146#usize from by decide,if_false,
    mul,lift,drop,chunks,scan,prefixRead,verify,Bool.false_eq_true,Bool.true_eq,if_true]
  all_goals rfl
#print axioms source

theorem loop {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGr_M1Root.retainedRoot) 1#usize
      (JGu_Scratch1.s00 s).idx (JGu_Scratch1.s00 s).val hash 0#usize 10#usize 1#usize
      (JGu_Keys.keys 1) 0#usize 0#usize=
        ok ((JGu_Verify1.output D hash s).idx,(JGu_Verify1.output D hash s).val,some (.Ok ())) := by
  apply (JGu_Scratch1.source D hash (encodeState JGr_M1Root.retainedRoot) s).trans
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGr_M1Root.retainedRoot) 1#usize
      (JGu_Scratch1.s10 s).idx (JGu_Scratch1.s10 s).val hash 0#usize 10#usize 1#usize
      (JGu_Keys.keys 1) 10#usize 10#usize=_
  conv_lhs =>
    unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
    rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,source,bind_tc_ok]
#print axioms loop

end AspisR1.JGw_Terminal1
end
