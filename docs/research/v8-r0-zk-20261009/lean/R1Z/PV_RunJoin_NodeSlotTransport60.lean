import R1Z.PV_RunJoin_NodeSlotRead60
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NodeSlotTransport60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PublishSkeleton54
variable [ExternalTypes] [ExternalFuns]

theorem complete (out : alloc.vec.Vec U8) (cc1 cc2 : host_commitment.Commitment)
    (tree : host_tree.BinaryTree) (queries : Array U32 22#usize) (batch t cap : Usize)
    (read : PV_RunJoin_NodeSlotRead60.Read batch t cap)
    (room : out.length+2*cap.val≤Usize.max) :
    resultBytes (prover.append_node_slot out cc1 cc2 tree queries batch t)=
      exceptBytes (ProverCommitPublish43.appendSlot (bytes out.val)
        (PV_RunJoin_NodePayloadModel60.model (PV_RunJoin_NodePayload60.payload cc1 cc2 tree queries batch t) cap.val)) := by
  rw [PV_RunJoin_NodeSlotRead60.source out cc1 cc2 tree queries batch t cap read]
  exact PV_RunJoin_NodePayloadModel60.complete out _ cap room

#print axioms complete
end R1Z.PV_RunJoin_NodeSlotTransport60
