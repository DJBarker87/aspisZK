import NDO_JGk_TX2_CountSource
import NDO_JGm_TX2_PaddingCalls
import NDO_JGm_TX2_Verify
import Port4B_Bounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Terminal0
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGf_TX2_M0Root.retainedRoot) 0#usize hash
      10#usize 12#usize 3#usize (JGk_TX2_ScratchKeys.keys 0)
      (JGk_TX2_Scratch0.s12 s).idx (JGk_TX2_Scratch0.s12 s).val 12#usize 12#usize=
        ok (.done ((JGm_TX2_Verify0.output D hash s).idx,(JGm_TX2_Verify0.output D hash s).val,some (.Ok ()))) := by
  have frontRead : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      (JGk_TX2_Scratch0.s12 s).idx {«end»:=12#usize}=ok (JGk_TX2_CountSource.front0 s) := by
    simp only [Array.index_SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index]
    rw [if_pos (by change (12:Nat)≤(JGk_TX2_Scratch0.s12 s).idx.val.length;rw [(JGk_TX2_Scratch0.s12 s).idx.property];decide)]
    rfl
  have mul : Usize.wrapping_mul 32#usize 163#usize=5216#usize := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_mul_val_eq]
    apply Nat.mod_eq_of_lt
    rw [UScalar.size_def]
    scalar_tac
  have drop : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      JGh_TX2_NodeViews.nodes0 {start:=5216#usize}=ok JGm_TX2_PaddingCalls.padding0 :=
    MultiproofConeSlices.drop_total _ _ (by rw [JGh_TX2_NodeViews.length0];decide)
  have prefixRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      JGh_TX2_NodeViews.nodes0 {«end»:=5216#usize}=ok JGm_TX2_Supplied.nodes0 :=
    MultiproofConeSlices.prefix_total _ _ (by rw [JGh_TX2_NodeViews.length0];decide)
  obtain ⟨ce,after,chunks,scan⟩ := JGm_TX2_PaddingCalls.source (JGc_TX2_RealLeaves.dictionary D)
    JGm_TX2_PaddingCalls.padding0 JGm_TX2_PaddingCalls.bytes0
  simp only [Port3_BatchStd.install] at scan
  have verify : Port4B_Install.leaves.op10 (JGc_TX2_RealLeaves.dictionary D) hash .Two
      (encodeState JGf_TX2_M0Root.retainedRoot)
      (JGk_TX2_Scratch0.s12 s).idx (JGk_TX2_Scratch0.s12 s).val 12#usize JGm_TX2_Supplied.nodes0=
      ok (true,(JGm_TX2_Verify0.output D hash s).idx,(JGm_TX2_Verify0.output D hash s).val) := by
    change (do
      let (b,out) ← reference.verify_owned
        (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
        (encodeState JGf_TX2_M0Root.retainedRoot) (JGk_TX2_Scratch0.s12 s) JGm_TX2_Supplied.nodes0
      ok (b,out.idx,out.val))=_
    rw [JGm_TX2_Verify0.source D hash s]
    rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body,
    if_neg (by decide : ¬12#usize<12#usize),frontRead]
  have countRead := JGk_TX2_CountSource.source0 s
  have nodeRead := JGh_TX2_NodeViews.source0
  change Port4B_Install.leaves.op11 .Two _=_ at countRead
  simp only [bind_tc_ok,Port3_BatchStd.install,countRead,Port3_BatchStd.okOr,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [nodeRead]
  simp only [bind_tc_ok]
  have cap : Array.index_usize
      (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize])
      3#usize=ok 172#usize := by rfl
  rw [cap]
  simp only [bind_tc_ok,show ¬163#usize>172#usize from by decide,if_false,
    mul,lift,drop,chunks,scan,prefixRead,verify,Bool.false_eq_true,Bool.true_eq,if_true]
  all_goals rfl
#print axioms source

theorem loop {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGf_TX2_M0Root.retainedRoot) 0#usize
      (JGk_TX2_Scratch0.s00 s).idx (JGk_TX2_Scratch0.s00 s).val hash 10#usize 12#usize 3#usize
      (JGk_TX2_ScratchKeys.keys 0) 0#usize 0#usize=
        ok ((JGm_TX2_Verify0.output D hash s).idx,(JGm_TX2_Verify0.output D hash s).val,some (.Ok ())) := by
  apply (JGk_TX2_Scratch0.source D hash (encodeState JGf_TX2_M0Root.retainedRoot) s).trans
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGf_TX2_M0Root.retainedRoot) 0#usize
      (JGk_TX2_Scratch0.s12 s).idx (JGk_TX2_Scratch0.s12 s).val hash 10#usize 12#usize 3#usize
      (JGk_TX2_ScratchKeys.keys 0) 12#usize 12#usize=_
  conv_lhs =>
    unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
    rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,source,bind_tc_ok]
#print axioms loop

theorem tree {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState JGf_TX2_M0Root.retainedRoot)
      1#usize 0#usize s.idx s.val hash=
        ok (.Ok (), (JGm_TX2_Verify0.output D hash s).idx,(JGm_TX2_Verify0.output D hash s).val) := by
  have splitCount : Usize.wrapping_sub 22#usize 10#usize=12#usize :=
    UScalar.eq_of_val_eq (by simpa only [show (12#usize).val=12 from rfl,Port4B_TreeCuts.count,Port4B_TreeCuts.hi,Port4B_TreeCuts.lo,
      show ¬1#usize=0#usize from by decide,if_false] using (Port4B_Bounds.count 1#usize).1)
  have slot : Usize.wrapping_add (Usize.wrapping_mul 3#usize 1#usize) 0#usize=3#usize :=
    UScalar.eq_of_val_eq (Port4B_Bounds.slot 1#usize 0#usize (by decide) (by decide))
  have lo : (Port3_BatchStd.install Port4B_Install.leaves).op13=ok 10#usize := rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree,if_neg (by decide : ¬1#usize=0#usize)]
  simp only [lo,bind_tc_ok,lift,splitCount,slot]
  change (do
    let a ← (Port3_BatchStd.install Port4B_Install.leaves).op4 JFo_Prepared.value.queries
      10#usize (Usize.wrapping_sub 22#usize 10#usize) 0#usize
    let keys ← (Port3_BatchStd.install Port4B_Install.leaves).op5 a (Usize.wrapping_sub 22#usize 10#usize)
    let (idx,val,pending) ← Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGf_TX2_M0Root.retainedRoot) 0#usize
      s.idx s.val hash 10#usize (Usize.wrapping_sub 22#usize 10#usize) 3#usize keys 0#usize 0#usize
    match pending with
    | none => fail .panic
    | some r => ok (r,idx,val))=_
  rw [splitCount]
  have build : (Port3_BatchStd.install Port4B_Install.leaves).op4 JFo_Prepared.value.queries
      10#usize 12#usize 0#usize=ok (JGf_TX2_Keys.raw 0) := JGf_TX2_Keys.source 0#usize (by decide)
  have sort : (Port3_BatchStd.install Port4B_Install.leaves).op5 (JGf_TX2_Keys.raw 0) 12#usize=
      ok (JGk_TX2_ScratchKeys.keys 0) := JGk_TX2_ScratchKeys.returned 0
  rw [build,bind_tc_ok,sort,bind_tc_ok]
  have run := loop D hash s
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGf_TX2_M0Root.retainedRoot) 0#usize
      s.idx s.val hash 10#usize 12#usize 3#usize (JGk_TX2_ScratchKeys.keys 0) 0#usize 0#usize=_ at run
  rw [run]
  rfl
#print axioms tree
end AspisR1.JGm_TX2_Terminal0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Terminal1
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes1

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGh_TX2_M1Root.retainedRoot) 1#usize hash
      10#usize 12#usize 4#usize (JGk_TX2_ScratchKeys.keys 1)
      (JGk_TX2_Scratch1.s12 s).idx (JGk_TX2_Scratch1.s12 s).val 12#usize 12#usize=
        ok (.done ((JGm_TX2_Verify1.output D hash s).idx,(JGm_TX2_Verify1.output D hash s).val,some (.Ok ()))) := by
  have frontRead : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      (JGk_TX2_Scratch1.s12 s).idx {«end»:=12#usize}=ok (JGk_TX2_CountSource.front1 s) := by
    simp only [Array.index_SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index]
    rw [if_pos (by change (12:Nat)≤(JGk_TX2_Scratch1.s12 s).idx.val.length;rw [(JGk_TX2_Scratch1.s12 s).idx.property];decide)]
    rfl
  have mul : Usize.wrapping_mul 32#usize 163#usize=5216#usize := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_mul_val_eq]
    apply Nat.mod_eq_of_lt
    rw [UScalar.size_def]
    scalar_tac
  have drop : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      JGh_TX2_NodeViews.nodes1 {start:=5216#usize}=ok JGm_TX2_PaddingCalls.padding1 :=
    MultiproofConeSlices.drop_total _ _ (by rw [JGh_TX2_NodeViews.length1];decide)
  have prefixRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      JGh_TX2_NodeViews.nodes1 {«end»:=5216#usize}=ok JGm_TX2_Supplied.nodes1 :=
    MultiproofConeSlices.prefix_total _ _ (by rw [JGh_TX2_NodeViews.length1];decide)
  obtain ⟨ce,after,chunks,scan⟩ := JGm_TX2_PaddingCalls.source (JGc_TX2_RealLeaves.dictionary D)
    JGm_TX2_PaddingCalls.padding1 JGm_TX2_PaddingCalls.bytes1
  simp only [Port3_BatchStd.install] at scan
  have verify : Port4B_Install.leaves.op10 (JGc_TX2_RealLeaves.dictionary D) hash .Two
      (encodeState JGh_TX2_M1Root.retainedRoot)
      (JGk_TX2_Scratch1.s12 s).idx (JGk_TX2_Scratch1.s12 s).val 12#usize JGm_TX2_Supplied.nodes1=
      ok (true,(JGm_TX2_Verify1.output D hash s).idx,(JGm_TX2_Verify1.output D hash s).val) := by
    change (do
      let (b,out) ← reference.verify_owned
        (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
        (encodeState JGh_TX2_M1Root.retainedRoot) (JGk_TX2_Scratch1.s12 s) JGm_TX2_Supplied.nodes1
      ok (b,out.idx,out.val))=_
    rw [JGm_TX2_Verify1.source D hash s]
    rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body,
    if_neg (by decide : ¬12#usize<12#usize),frontRead]
  have countRead := JGk_TX2_CountSource.source1 s
  have nodeRead := JGh_TX2_NodeViews.source1
  change Port4B_Install.leaves.op11 .Two _=_ at countRead
  simp only [bind_tc_ok,Port3_BatchStd.install,countRead,Port3_BatchStd.okOr,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [nodeRead]
  simp only [bind_tc_ok]
  have cap : Array.index_usize
      (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize])
      4#usize=ok 172#usize := by rfl
  rw [cap]
  simp only [bind_tc_ok,show ¬163#usize>172#usize from by decide,if_false,
    mul,lift,drop,chunks,scan,prefixRead,verify,Bool.false_eq_true,Bool.true_eq,if_true]
  all_goals rfl
#print axioms source

theorem loop {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGh_TX2_M1Root.retainedRoot) 1#usize
      (JGk_TX2_Scratch1.s00 s).idx (JGk_TX2_Scratch1.s00 s).val hash 10#usize 12#usize 4#usize
      (JGk_TX2_ScratchKeys.keys 1) 0#usize 0#usize=
        ok ((JGm_TX2_Verify1.output D hash s).idx,(JGm_TX2_Verify1.output D hash s).val,some (.Ok ())) := by
  apply (JGk_TX2_Scratch1.source D hash (encodeState JGh_TX2_M1Root.retainedRoot) s).trans
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGh_TX2_M1Root.retainedRoot) 1#usize
      (JGk_TX2_Scratch1.s12 s).idx (JGk_TX2_Scratch1.s12 s).val hash 10#usize 12#usize 4#usize
      (JGk_TX2_ScratchKeys.keys 1) 12#usize 12#usize=_
  conv_lhs =>
    unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
    rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,source,bind_tc_ok]
#print axioms loop

theorem tree {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState JGh_TX2_M1Root.retainedRoot)
      1#usize 1#usize s.idx s.val hash=
        ok (.Ok (), (JGm_TX2_Verify1.output D hash s).idx,(JGm_TX2_Verify1.output D hash s).val) := by
  have splitCount : Usize.wrapping_sub 22#usize 10#usize=12#usize :=
    UScalar.eq_of_val_eq (by simpa only [show (12#usize).val=12 from rfl,Port4B_TreeCuts.count,Port4B_TreeCuts.hi,Port4B_TreeCuts.lo,
      show ¬1#usize=0#usize from by decide,if_false] using (Port4B_Bounds.count 1#usize).1)
  have slot : Usize.wrapping_add (Usize.wrapping_mul 3#usize 1#usize) 1#usize=4#usize :=
    UScalar.eq_of_val_eq (Port4B_Bounds.slot 1#usize 1#usize (by decide) (by decide))
  have lo : (Port3_BatchStd.install Port4B_Install.leaves).op13=ok 10#usize := rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree,if_neg (by decide : ¬1#usize=0#usize)]
  simp only [lo,bind_tc_ok,lift,splitCount,slot]
  change (do
    let a ← (Port3_BatchStd.install Port4B_Install.leaves).op4 JFo_Prepared.value.queries
      10#usize (Usize.wrapping_sub 22#usize 10#usize) 1#usize
    let keys ← (Port3_BatchStd.install Port4B_Install.leaves).op5 a (Usize.wrapping_sub 22#usize 10#usize)
    let (idx,val,pending) ← Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGh_TX2_M1Root.retainedRoot) 1#usize
      s.idx s.val hash 10#usize (Usize.wrapping_sub 22#usize 10#usize) 4#usize keys 0#usize 0#usize
    match pending with
    | none => fail .panic
    | some r => ok (r,idx,val))=_
  rw [splitCount]
  have build : (Port3_BatchStd.install Port4B_Install.leaves).op4 JFo_Prepared.value.queries
      10#usize 12#usize 1#usize=ok (JGf_TX2_Keys.raw 1) := JGf_TX2_Keys.source 1#usize (by decide)
  have sort : (Port3_BatchStd.install Port4B_Install.leaves).op5 (JGf_TX2_Keys.raw 1) 12#usize=
      ok (JGk_TX2_ScratchKeys.keys 1) := JGk_TX2_ScratchKeys.returned 1
  rw [build,bind_tc_ok,sort,bind_tc_ok]
  have run := loop D hash s
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGh_TX2_M1Root.retainedRoot) 1#usize
      s.idx s.val hash 10#usize 12#usize 4#usize (JGk_TX2_ScratchKeys.keys 1) 0#usize 0#usize=_ at run
  rw [run]
  rfl
#print axioms tree
end AspisR1.JGm_TX2_Terminal1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Terminal2
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes2

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGc_TX2_M2Root.retainedRoot) 2#usize hash
      10#usize 12#usize 5#usize (JGk_TX2_ScratchKeys.keys 2)
      (JGk_TX2_Scratch2.s12 s).idx (JGk_TX2_Scratch2.s12 s).val 12#usize 12#usize=
        ok (.done ((JGm_TX2_Verify2.output D hash s).idx,(JGm_TX2_Verify2.output D hash s).val,some (.Ok ()))) := by
  have frontRead : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      (JGk_TX2_Scratch2.s12 s).idx {«end»:=12#usize}=ok (JGk_TX2_CountSource.front2 s) := by
    simp only [Array.index_SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index]
    rw [if_pos (by change (12:Nat)≤(JGk_TX2_Scratch2.s12 s).idx.val.length;rw [(JGk_TX2_Scratch2.s12 s).idx.property];decide)]
    rfl
  have mul : Usize.wrapping_mul 32#usize 141#usize=4512#usize := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_mul_val_eq]
    apply Nat.mod_eq_of_lt
    rw [UScalar.size_def]
    scalar_tac
  have drop : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      JGh_TX2_NodeViews.nodes2 {start:=4512#usize}=ok JGm_TX2_PaddingCalls.padding2 :=
    MultiproofConeSlices.drop_total _ _ (by rw [JGh_TX2_NodeViews.length2];decide)
  have prefixRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      JGh_TX2_NodeViews.nodes2 {«end»:=4512#usize}=ok JGm_TX2_Supplied.nodes2 :=
    MultiproofConeSlices.prefix_total _ _ (by rw [JGh_TX2_NodeViews.length2];decide)
  obtain ⟨ce,after,chunks,scan⟩ := JGm_TX2_PaddingCalls.source (JGc_TX2_RealLeaves.dictionary D)
    JGm_TX2_PaddingCalls.padding2 JGm_TX2_PaddingCalls.bytes2
  simp only [Port3_BatchStd.install] at scan
  have verify : Port4B_Install.leaves.op10 (JGc_TX2_RealLeaves.dictionary D) hash .Two
      (encodeState JGc_TX2_M2Root.retainedRoot)
      (JGk_TX2_Scratch2.s12 s).idx (JGk_TX2_Scratch2.s12 s).val 12#usize JGm_TX2_Supplied.nodes2=
      ok (true,(JGm_TX2_Verify2.output D hash s).idx,(JGm_TX2_Verify2.output D hash s).val) := by
    change (do
      let (b,out) ← reference.verify_owned
        (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
        (encodeState JGc_TX2_M2Root.retainedRoot) (JGk_TX2_Scratch2.s12 s) JGm_TX2_Supplied.nodes2
      ok (b,out.idx,out.val))=_
    rw [JGm_TX2_Verify2.source D hash s]
    rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body,
    if_neg (by decide : ¬12#usize<12#usize),frontRead]
  have countRead := JGk_TX2_CountSource.source2 s
  have nodeRead := JGh_TX2_NodeViews.source2
  change Port4B_Install.leaves.op11 .Two _=_ at countRead
  simp only [bind_tc_ok,Port3_BatchStd.install,countRead,Port3_BatchStd.okOr,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [nodeRead]
  simp only [bind_tc_ok]
  have cap : Array.index_usize
      (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize])
      5#usize=ok 150#usize := by rfl
  rw [cap]
  simp only [bind_tc_ok,show ¬141#usize>150#usize from by decide,if_false,
    mul,lift,drop,chunks,scan,prefixRead,verify,Bool.false_eq_true,Bool.true_eq,if_true]
  all_goals rfl
#print axioms source

theorem loop {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGc_TX2_M2Root.retainedRoot) 2#usize
      (JGk_TX2_Scratch2.s00 s).idx (JGk_TX2_Scratch2.s00 s).val hash 10#usize 12#usize 5#usize
      (JGk_TX2_ScratchKeys.keys 2) 0#usize 0#usize=
        ok ((JGm_TX2_Verify2.output D hash s).idx,(JGm_TX2_Verify2.output D hash s).val,some (.Ok ())) := by
  apply (JGk_TX2_Scratch2.source D hash (encodeState JGc_TX2_M2Root.retainedRoot) s).trans
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGc_TX2_M2Root.retainedRoot) 2#usize
      (JGk_TX2_Scratch2.s12 s).idx (JGk_TX2_Scratch2.s12 s).val hash 10#usize 12#usize 5#usize
      (JGk_TX2_ScratchKeys.keys 2) 12#usize 12#usize=_
  conv_lhs =>
    unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
    rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,source,bind_tc_ok]
#print axioms loop

theorem tree {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState JGc_TX2_M2Root.retainedRoot)
      1#usize 2#usize s.idx s.val hash=
        ok (.Ok (), (JGm_TX2_Verify2.output D hash s).idx,(JGm_TX2_Verify2.output D hash s).val) := by
  have splitCount : Usize.wrapping_sub 22#usize 10#usize=12#usize :=
    UScalar.eq_of_val_eq (by simpa only [show (12#usize).val=12 from rfl,Port4B_TreeCuts.count,Port4B_TreeCuts.hi,Port4B_TreeCuts.lo,
      show ¬1#usize=0#usize from by decide,if_false] using (Port4B_Bounds.count 1#usize).1)
  have slot : Usize.wrapping_add (Usize.wrapping_mul 3#usize 1#usize) 2#usize=5#usize :=
    UScalar.eq_of_val_eq (Port4B_Bounds.slot 1#usize 2#usize (by decide) (by decide))
  have lo : (Port3_BatchStd.install Port4B_Install.leaves).op13=ok 10#usize := rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree,if_neg (by decide : ¬1#usize=0#usize)]
  simp only [lo,bind_tc_ok,lift,splitCount,slot]
  change (do
    let a ← (Port3_BatchStd.install Port4B_Install.leaves).op4 JFo_Prepared.value.queries
      10#usize (Usize.wrapping_sub 22#usize 10#usize) 2#usize
    let keys ← (Port3_BatchStd.install Port4B_Install.leaves).op5 a (Usize.wrapping_sub 22#usize 10#usize)
    let (idx,val,pending) ← Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGc_TX2_M2Root.retainedRoot) 2#usize
      s.idx s.val hash 10#usize (Usize.wrapping_sub 22#usize 10#usize) 5#usize keys 0#usize 0#usize
    match pending with
    | none => fail .panic
    | some r => ok (r,idx,val))=_
  rw [splitCount]
  have build : (Port3_BatchStd.install Port4B_Install.leaves).op4 JFo_Prepared.value.queries
      10#usize 12#usize 2#usize=ok (JGf_TX2_Keys.raw 2) := JGf_TX2_Keys.source 2#usize (by decide)
  have sort : (Port3_BatchStd.install Port4B_Install.leaves).op5 (JGf_TX2_Keys.raw 2) 12#usize=
      ok (JGk_TX2_ScratchKeys.keys 2) := JGk_TX2_ScratchKeys.returned 2
  rw [build,bind_tc_ok,sort,bind_tc_ok]
  have run := loop D hash s
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JGc_TX2_M2Root.retainedRoot) 2#usize
      s.idx s.val hash 10#usize 12#usize 5#usize (JGk_TX2_ScratchKeys.keys 2) 0#usize 0#usize=_ at run
  rw [run]
  rfl
#print axioms tree
end AspisR1.JGm_TX2_Terminal2
end
