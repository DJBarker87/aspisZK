import R1Z.PV_RunJoin_NodePayload60
import R1Z.PV_RunJoin_NodePayloadModel60
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NodeSlotRead60
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def Read (batch t cap : Usize) : Prop :=
  (do let caps ← compact.SLOT_NODES
      let size ← Array.index_usize caps (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) t)
      ok (Usize.wrapping_mul 32#usize size))=ok cap

theorem source (out : alloc.vec.Vec U8) (cc1 cc2 : host_commitment.Commitment)
    (tree : host_tree.BinaryTree) (queries : Array U32 22#usize) (batch t cap : Usize)
    (read : Read batch t cap) :
    prover.append_node_slot out cc1 cc2 tree queries batch t=
      PV_RunJoin_NodePayloadModel60.run out (PV_RunJoin_NodePayload60.payload cc1 cc2 tree queries batch t) cap := by
  rw [PV_RunJoin_NodePayload60.source]
  unfold PV_RunJoin_NodePayloadModel60.run
  apply PV_RunJoin_ResultBindEq55.complete
  intro status
  cases status with
  | Err e => rfl
  | Ok nodes =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    have h := congrArg (fun r : Result Usize => do
      let cap ← r
      let next ← PV_RunJoin_NodeTail41.finish out nodes cap
      ok (core.result.Result.Ok next : core.result.Result (alloc.vec.Vec U8) verifier.Error)) read
    simpa only [Read,bind_assoc_eq,bind_tc_ok] using h

#print axioms source
end R1Z.PV_RunJoin_NodeSlotRead60
