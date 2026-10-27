import JGr_Keys
import JGk_TX2_LeafPush
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_Keys
open Aeneas Aeneas.Std Result MultiproofConeRef

def positions : List Nat := [6,0,1,9,7,5,8,4,2,3]
def keys (kind : Nat) : Array U64 16#usize := Classical.choose (JGr_Keys.source kind)
theorem returned (kind : Nat) : Port4B_Install.leaves.op5 (JGr_Keys.raw kind) 10#usize=ok (keys kind) :=
  (Classical.choose_spec (JGr_Keys.source kind)).1
#print axioms returned

theorem sorted0 : OraclePortFrozenOrder.sortedPositions JGr_Keys.q 0 0=positions := by rfl
#print axioms sorted0
theorem sorted1 : OraclePortFrozenOrder.sortedPositions JGr_Keys.q 0 1=positions := by rfl
#print axioms sorted1
theorem sorted2 : OraclePortFrozenOrder.sortedPositions JGr_Keys.q 0 2=positions := by rfl
#print axioms sorted2

theorem stream0 : Port4B_LeafLoop.KeyStream JGr_Keys.q 0 0 (keys 0) 0#usize positions := by
  rw [←sorted0]
  exact (Classical.choose_spec (JGr_Keys.source 0)).2
#print axioms stream0
theorem stream1 : Port4B_LeafLoop.KeyStream JGr_Keys.q 0 1 (keys 1) 0#usize positions := by
  rw [←sorted1]
  exact (Classical.choose_spec (JGr_Keys.source 1)).2
#print axioms stream1
theorem stream2 : Port4B_LeafLoop.KeyStream JGr_Keys.q 0 2 (keys 2) 0#usize positions := by
  rw [←sorted2]
  exact (Classical.choose_spec (JGr_Keys.source 2)).2
#print axioms stream2
end AspisR1.JGu_Keys
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_Keys
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem advance_loop {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (kind slot pos next : Usize) (s t : reference.Scratch)
    (body : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root kind hash 0#usize 10#usize slot (keys kind.val)
      s.idx s.val s.n pos=ok (.cont (t.idx,t.val,t.n,next))) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root kind s.idx s.val hash 0#usize 10#usize slot (keys kind.val) s.n pos=
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root kind t.idx t.val hash 0#usize 10#usize slot (keys kind.val) t.n next := by
  conv_lhs =>
    unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
    rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,body,bind_tc_ok]
  rfl
#print axioms advance_loop
end AspisR1.JGu_Keys
end
