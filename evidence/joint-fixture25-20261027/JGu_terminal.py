from pathlib import Path
P=Path(__file__).resolve().parent;R=P.parents[1]
for t,count in [(0,138),(1,138),(2,120)]:
 off=32*count;cap=146 if t<2 else 128;ct=0 if t<2 else 2;root=f'JGr_M{t}Root.retainedRoot';ns=f'JGu_Terminal{t}'
 s=f'''import JGu_Levels{t}
import JGu_PaddingScan
import JGr_Counts
import Port4B_Bounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGp_Slot{t}.value

theorem source {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState {root}) {t}#usize hash
      0#usize 10#usize {t}#usize (JGu_Keys.keys {t})
      (JGu_Scratch{t}.s10 s).idx (JGu_Scratch{t}.s10 s).val 10#usize 10#usize=
        ok (.done ((JGu_Verify{t}.output D hash s).idx,(JGu_Verify{t}.output D hash s).val,some (.Ok ()))) := by
  have frontRead : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      (JGu_Scratch{t}.s10 s).idx {{«end»:=10#usize}}=ok JGr_Count{ct}.frontier := by
    simp only [Array.index_SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index]
    rw [if_pos (by change (10:Nat)≤(JGu_Scratch{t}.s10 s).idx.val.length;rw [(JGu_Scratch{t}.s10 s).idx.property];decide)]
    apply congrArg ok
    apply Subtype.ext
    exact JGu_Initial{t}.idx10 s
  have mul : Usize.wrapping_mul 32#usize {count}#usize={off}#usize := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_mul_val_eq]
    apply Nat.mod_eq_of_lt
    rw [UScalar.size_def]
    scalar_tac
  have fits : ({off}#usize).val≤JGp_Slot{t}.value.val.length := by
    have len : JGp_Slot{t}.value.val.length={cap*32} := JGp_Slot{t}.length
    rw [len]
    decide
  have drop : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      JGp_Slot{t}.value {{start:={off}#usize}}=ok JGu_Padding{t}.padding :=
    MultiproofConeSlices.drop_total _ _ fits
  have prefixRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      JGp_Slot{t}.value {{«end»:={off}#usize}}=ok JGu_Supplied.nodes{t} :=
    MultiproofConeSlices.prefix_total _ _ fits
  obtain ⟨ce,after,chunks,scan⟩ := JGu_PaddingScan.calls (JGc_TX2_RealLeaves.dictionary D)
    JGu_Padding{t}.padding JGu_Padding{t}.bytes
  simp only [Port3_BatchStd.install] at scan
  have verify : Port4B_Install.leaves.op10 (JGc_TX2_RealLeaves.dictionary D) hash .Two
      (encodeState {root})
      (JGu_Scratch{t}.s10 s).idx (JGu_Scratch{t}.s10 s).val 10#usize JGu_Supplied.nodes{t}=
      ok (true,(JGu_Verify{t}.output D hash s).idx,(JGu_Verify{t}.output D hash s).val) := by
    change (do
      let (b,out) ← reference.verify_owned
        (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
        (encodeState {root}) (JGu_Scratch{t}.s10 s) JGu_Supplied.nodes{t}
      ok (b,out.idx,out.val))=_
    rw [JGu_Verify{t}.source D hash s]
    rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body,
    if_neg (by decide : ¬10#usize<10#usize),frontRead]
  have countRead := JGr_Count{ct}.source
  have nodeRead := JGp_Slot{t}.source
  change Port4B_Install.leaves.op11 .Two _=_ at countRead
  simp only [bind_tc_ok,Port3_BatchStd.install,countRead,Port3_BatchStd.okOr,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [nodeRead]
  simp only [bind_tc_ok]
  have capacity : Array.index_usize
      (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize])
      {t}#usize=ok {cap}#usize := rfl
  rw [capacity]
  simp only [bind_tc_ok,show ¬{count}#usize>{cap}#usize from by decide,if_false,
    mul,lift,drop,chunks,scan,prefixRead,verify,Bool.false_eq_true,Bool.true_eq,if_true]
  all_goals rfl
#print axioms source

theorem loop {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState {root}) {t}#usize
      (JGu_Scratch{t}.s00 s).idx (JGu_Scratch{t}.s00 s).val hash 0#usize 10#usize {t}#usize
      (JGu_Keys.keys {t}) 0#usize 0#usize=
        ok ((JGu_Verify{t}.output D hash s).idx,(JGu_Verify{t}.output D hash s).val,some (.Ok ())) := by
  apply (JGu_Scratch{t}.source D hash (encodeState {root}) s).trans
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState {root}) {t}#usize
      (JGu_Scratch{t}.s10 s).idx (JGu_Scratch{t}.s10 s).val hash 0#usize 10#usize {t}#usize
      (JGu_Keys.keys {t}) 10#usize 10#usize=_
  conv_lhs =>
    unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
    rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,source,bind_tc_ok]
#print axioms loop

theorem tree {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState {root})
      0#usize {t}#usize s.idx s.val hash=
        ok (.Ok (), (JGu_Verify{t}.output D hash s).idx,(JGu_Verify{t}.output D hash s).val) := by
  have splitCount : Usize.wrapping_sub 10#usize 0#usize=10#usize := rfl
  have slot : Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) {t}#usize={t}#usize := rfl
  have hi : (Port3_BatchStd.install Port4B_Install.leaves).op13=ok 10#usize := rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree,if_pos rfl]
  simp only [hi,bind_tc_ok,lift,splitCount,slot]
  have build : (Port3_BatchStd.install Port4B_Install.leaves).op4 JFo_Prepared.value.queries
      0#usize 10#usize {t}#usize=ok (JGr_Keys.raw {t}) := JGr_Keys.build {t}#usize (by decide)
  have sort : (Port3_BatchStd.install Port4B_Install.leaves).op5 (JGr_Keys.raw {t}) 10#usize=
      ok (JGu_Keys.keys {t}) := JGu_Keys.returned {t}
  rw [build,bind_tc_ok,sort,bind_tc_ok]
  have run := loop D hash s
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState {root}) {t}#usize
      s.idx s.val hash 0#usize 10#usize {t}#usize (JGu_Keys.keys {t}) 0#usize 0#usize=_ at run
  rw [run]
  rfl
#print axioms tree
end AspisR1.{ns}
end
'''
 (R/f'lean/{ns}.lean').write_text(s)
print('Generated exact terminal loops and batch0 trees')
