import R1Z.PV_RunJoin_TransferPrefix2021
import R1Z.PV_RunJoin_WithdrawalPrefix2021
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublicRoots21
open R0Z.WriterRefine PV_RunJoin_FixtureRecords
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation AspisR1.AppendPath.pathPrefix

theorem transfer : PV_RunJoin_PublicCore21.transfer.nextRoot = (fixturePublic false).nextRoot := by
  change digK (K := M) PV_RunJoin_RecordedTransfer.transition.candidate_afterstate.next_root =
    AspisR1.AppendPath.pathPrefix (base false) (outputPair false) 20
  rw [← PV_RunJoin_TransferPrefix2021.source]
  funext i; fin_cases i <;> rfl
#print axioms transfer

theorem withdrawal : PV_RunJoin_PublicCore21.withdrawal.nextRoot = (fixturePublic true).nextRoot := by
  change digK (K := M) PV_RunJoin_RecordedWithdrawal.transition.candidate_afterstate.next_root =
    AspisR1.AppendPath.pathPrefix (base true) (outputPair true) 20
  rw [← PV_RunJoin_WithdrawalPrefix2021.source]
  funext i; fin_cases i <;> rfl
#print axioms withdrawal
end R1Z.PV_RunJoin_PublicRoots21
