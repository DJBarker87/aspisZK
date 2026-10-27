import R1Z.PV_RunJoin_PairModel21
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TransferFrontier1621
open R0Z.WriterRefine PV_RunJoin_FixtureRecords
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation
/-- Sparse zero-index frontier: an unchanged frozen-empty cell. -/
theorem source : PV_RunJoin_PublicCore21.transfer.nextFrontier ⟨16,by decide⟩ =
    (fixturePublic false).nextFrontier ⟨16,by decide⟩ := by
  change digK (K := M) (PV_RunJoin_RecordedTransfer.transition.candidate_afterstate.next_frontier.val[16]!) =
    AspisR1.AppendNode.frozenEmpty (⟨16,by decide⟩ : Fin 21)
  rw [PV_RunJoin_RootModel.frozen_literal]
  funext i; fin_cases i <;> rfl
#print axioms source
end R1Z.PV_RunJoin_TransferFrontier1621
