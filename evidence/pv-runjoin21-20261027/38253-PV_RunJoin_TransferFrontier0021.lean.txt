import R1Z.PV_RunJoin_PairModel21
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TransferFrontier0021
open R0Z.WriterRefine PV_RunJoin_FixtureRecords
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation
/-- Sparse zero-index frontier: the changed carry cell. -/
theorem source : PV_RunJoin_PublicCore21.transfer.nextFrontier ⟨0,by decide⟩ =
    (fixturePublic false).nextFrontier ⟨0,by decide⟩ := by
  change digK (K := M) (PV_RunJoin_RecordedTransfer.transition.candidate_afterstate.next_frontier.val[0]!) = outputPair false
  rw [← PV_RunJoin_PairModel21.transfer]
  funext i; fin_cases i <;> rfl
#print axioms source
end R1Z.PV_RunJoin_TransferFrontier0021
