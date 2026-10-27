from pathlib import Path
R=Path(__file__).resolve().parents[2]
for t,pre,count in [(0,'JGf',163),(1,'JGh',163),(2,'JGc',141)]:
 ns=f'JGm_TX2_Terminal{t}';off=32*count
 s=f'''import JGm_TX2_Verify{t}
import JGm_TX2_PaddingCalls
import JGk_TX2_CountSource
import Port4B_Bounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes{t}

theorem source {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState {pre}_TX2_M{t}Root.retainedRoot) {t}#usize hash
      10#usize 12#usize {3+t}#usize (JGk_TX2_ScratchKeys.keys {t})
      (JGk_TX2_Scratch{t}.s12 s).idx (JGk_TX2_Scratch{t}.s12 s).val 12#usize 12#usize=
        ok (.done ((JGm_TX2_Verify{t}.output s).idx,(JGm_TX2_Verify{t}.output s).val,some (.Ok ()))) := by
  have frontRead : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      (JGk_TX2_Scratch{t}.s12 s).idx {{«end»:=12#usize}}=ok (JGk_TX2_CountSource.front{t} s) := by
    simp only [Array.index_SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index]
    rw [if_pos (by change (12:Nat)≤(JGk_TX2_Scratch{t}.s12 s).idx.val.length;rw [(JGk_TX2_Scratch{t}.s12 s).idx.property];decide)]
    rfl
  have mul : Usize.wrapping_mul 32#usize {count}#usize={off}#usize := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_mul_val_eq]
    apply Nat.mod_eq_of_lt
    rw [UScalar.size_def]
    scalar_tac
  have drop : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      JGh_TX2_NodeViews.nodes{t} {{start:={off}#usize}}=ok JGm_TX2_PaddingCalls.padding{t} :=
    MultiproofConeSlices.drop_total _ _ (by rw [JGh_TX2_NodeViews.length{t}];decide)
  have prefixRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      JGh_TX2_NodeViews.nodes{t} {{«end»:={off}#usize}}=ok JGm_TX2_Supplied.nodes{t} :=
    MultiproofConeSlices.prefix_total _ _ (by rw [JGh_TX2_NodeViews.length{t}];decide)
  obtain ⟨ce,after,chunks,scan⟩ := JGm_TX2_PaddingCalls.source (JGc_TX2_RealLeaves.dictionary D)
    JGm_TX2_PaddingCalls.padding{t} JGm_TX2_PaddingCalls.bytes{t}
  have verify : Port4B_Install.leaves.op10 (JGc_TX2_RealLeaves.dictionary D) hash .Two
      (encodeState {pre}_TX2_M{t}Root.retainedRoot)
      (JGk_TX2_Scratch{t}.s12 s).idx (JGk_TX2_Scratch{t}.s12 s).val 12#usize JGm_TX2_Supplied.nodes{t}=
      ok (true,(JGm_TX2_Verify{t}.output s).idx,(JGm_TX2_Verify{t}.output s).val) := by
    change (do let (b,out) ← reference.verify_owned
      (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (encodeState {pre}_TX2_M{t}Root.retainedRoot) (JGk_TX2_Scratch{t}.s12 s) JGm_TX2_Supplied.nodes{t}
               ok (b,out.idx,out.val))=_
    rw [JGm_TX2_Verify{t}.source D hash s]
    rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body,
    if_neg (by decide : ¬12#usize<12#usize),frontRead]
  have countRead := JGk_TX2_CountSource.source{t} s
  have nodeRead := JGh_TX2_NodeViews.source{t}
  change Port4B_Install.leaves.op11 .Two _=_ at countRead
  simp only [bind_tc_ok,Port3_BatchStd.install,countRead,Port3_BatchStd.okOr,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [nodeRead]
  simp only [bind_tc_ok]
  have cap : Array.index_usize
      (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize])
      {3+t}#usize=ok {172 if t<2 else 150}#usize := by rfl
  rw [cap]
  simp only [bind_tc_ok,show ¬{count}#usize>{172 if t<2 else 150}#usize from by decide,if_false,
    mul,lift,drop,chunks,scan,prefixRead,verify]
  rfl
#print axioms source

theorem loop {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState {pre}_TX2_M{t}Root.retainedRoot) {t}#usize
      (JGk_TX2_Scratch{t}.s00 s).idx (JGk_TX2_Scratch{t}.s00 s).val hash 10#usize 12#usize {3+t}#usize
      (JGk_TX2_ScratchKeys.keys {t}) 0#usize 0#usize=
        ok ((JGm_TX2_Verify{t}.output s).idx,(JGm_TX2_Verify{t}.output s).val,some (.Ok ())) := by
  rw [JGk_TX2_Scratch{t}.source]
  conv_lhs =>
    unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
    rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,source,bind_tc_ok]
  rfl
#print axioms loop

theorem tree {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState {pre}_TX2_M{t}Root.retainedRoot)
      1#usize {t}#usize s.idx s.val hash=
        ok (.Ok (), (JGm_TX2_Verify{t}.output s).idx,(JGm_TX2_Verify{t}.output s).val) := by
  have splitCount : Usize.wrapping_sub 22#usize 10#usize=12#usize :=
    UScalar.eq_of_val_eq (by simpa only [Port4B_TreeCuts.count,Port4B_TreeCuts.hi,Port4B_TreeCuts.lo,
      show ¬1#usize=0#usize from by decide,if_false] using (Port4B_Bounds.count 1#usize).1)
  have slot : Usize.wrapping_add (Usize.wrapping_mul 3#usize 1#usize) {t}#usize={3+t}#usize :=
    UScalar.eq_of_val_eq (Port4B_Bounds.slot 1#usize {t}#usize (by decide) (by decide))
  have lo : (Port3_BatchStd.install Port4B_Install.leaves).op13=ok 10#usize := rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree,if_neg (by decide : ¬1#usize=0#usize)]
  simp only [lo,bind_tc_ok,lift,splitCount,slot]
  have build := JGf_TX2_Keys.source {t}#usize (by decide)
  have sort := JGk_TX2_ScratchKeys.returned {t}
  rw [build,bind_tc_ok,sort,bind_tc_ok]
  have run := loop D hash s
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState {pre}_TX2_M{t}Root.retainedRoot) {t}#usize
      s.idx s.val hash 10#usize 12#usize {3+t}#usize (JGk_TX2_ScratchKeys.keys {t}) 0#usize 0#usize=_ at run
  rw [run]
  rfl
#print axioms tree
end AspisR1.{ns}
end
'''
 (R/f'lean/{ns}.lean').write_text(s)
print('Generated three native terminal/padding/leaf-loop joins')
