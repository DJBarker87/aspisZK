import R1Z.PV_Src_ReferenceWithdrawal
import R1Z.PV_Src_CanonicalRequest
import R1Z.PV_Src_CanonicalSibling

/-! Canonical withdrawal request amount follows admission; no public field is
changed to force record equality. Unused private recipient fields are erased. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_CanonicalWithdrawalRecord
open Aeneas Aeneas.Std Result R1J.SpendWitnessMap
open BuilderForestAdmissionPort.pool_v1
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem request (c : BuilderCanonical.Instance (K := K))
    (hv : c.val.1.variant = .withdrawal)
    (pool domain destination : PV_Src_PublicRecords.Context) :
    PV_Src_CanonicalRequest.request c pool domain destination =
      PV_Src_CheckedEncoding.withdrawalRequest
        (PV_Src_PublicRecords.withdrawal c.val.1 pool domain destination)
        (PV_Src_WithdrawalRecipient.erase c.val.2) := by
  simp only [PV_Src_CanonicalRequest.request,hv,
    PV_Src_CheckedEncoding.withdrawalRequest,PV_Src_PublicRecords.withdrawal,
    PV_Src_CanonicalRequest.amount c hv,Option.getD_some,
    PV_Src_CanonicalRequest.word_value,PV_Src_WithdrawalRecipient.erase]

theorem witness (c : BuilderCanonical.Instance (K := K))
    (hv : c.val.1.variant = .withdrawal)
    (roots : BuilderRecordsReference.Roots)
    (pool domain destination : PV_Src_PublicRecords.Context)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (anchor : Array U32 8#usize) :
    PV_Src_Forest_PrimitiveArguments.wordWitness
      (PV_Src_RecordReference.returned roots
        (PV_Src_CheckedEncoding.input (PV_Src_WithdrawalRecipient.erase c.val.2)
          (PV_Src_CanonicalRequest.request c pool domain destination)
          (PV_Src_PathIndex.index c.val.2) snapshot compiled anchor)).w =
      BuilderCanonical.rustWitness (PV_Src_WithdrawalRecipient.erase c.val.2) := by
  rw [request c hv]
  exact PV_Src_ReferenceWithdrawal.witness roots c.val.2
    (PV_Src_PublicRecords.withdrawal c.val.1 pool domain destination)
    snapshot compiled anchor (PV_Src_CanonicalSibling.sibling c)

#print axioms request
#print axioms witness
end R1Z.PV_Src_CanonicalWithdrawalRecord
