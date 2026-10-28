import NDO_JGk_TX2_PositionsExact
import NDO_JGk_TX2_LeafIteration
import JGk_TX2_LeafPush
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGk_TX2_ScratchKeys
open Aeneas Aeneas.Std Result MultiproofConeRef

def keys (kind : Nat) : Array U64 16#usize := Classical.choose (JGk_TX2_FrontierOrder.source kind)

theorem returned (kind : Nat) : Port4B_Install.leaves.op5 (JGf_TX2_Keys.raw kind) 12#usize=ok (keys kind) :=
  (Classical.choose_spec (JGk_TX2_FrontierOrder.source kind)).1
#print axioms returned

theorem stream0 : Port4B_LeafLoop.KeyStream JGk_TX2_FrontierOrder.q 1 0 (keys 0) 0#usize JGk_TX2_PositionsExact.positions := by
  rw [←JGk_TX2_PositionsExact.tree0]
  exact (Classical.choose_spec (JGk_TX2_FrontierOrder.source 0)).2
#print axioms stream0

theorem stream1 : Port4B_LeafLoop.KeyStream JGk_TX2_FrontierOrder.q 1 1 (keys 1) 0#usize JGk_TX2_PositionsExact.positions := by
  rw [←JGk_TX2_PositionsExact.tree1]
  exact (Classical.choose_spec (JGk_TX2_FrontierOrder.source 1)).2
#print axioms stream1

theorem stream2 : Port4B_LeafLoop.KeyStream JGk_TX2_FrontierOrder.q 1 2 (keys 2) 0#usize JGk_TX2_PositionsExact.positions := by
  rw [←JGk_TX2_PositionsExact.tree2]
  exact (Classical.choose_spec (JGk_TX2_FrontierOrder.source 2)).2
#print axioms stream2

theorem advance_loop {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (kind slot pos next : Usize) (s t : reference.Scratch)
    (body : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root kind hash 10#usize 12#usize slot (keys kind.val)
      s.idx s.val s.n pos=ok (.cont (t.idx,t.val,t.n,next))) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root kind s.idx s.val hash 10#usize 12#usize slot (keys kind.val) s.n pos=
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root kind t.idx t.val hash 10#usize 12#usize slot (keys kind.val) t.n next := by
  conv_lhs =>
    unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
    rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,body,bind_tc_ok]
  rfl
#print axioms advance_loop
end AspisR1.JGk_TX2_ScratchKeys
end
