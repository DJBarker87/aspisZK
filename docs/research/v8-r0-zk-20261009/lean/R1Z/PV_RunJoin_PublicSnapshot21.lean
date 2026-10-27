import R1Z.PV_RunJoin_PublicCore21
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublicSnapshot21
open R0Z.WriterRefine PV_RunJoin_FixtureRecords

theorem transfer : PV_RunJoin_PublicCore21.transfer.snapshotFrontier = (fixturePublic false).snapshotFrontier := by
  funext l
  change digK (K := M) (PV_RunJoin_RecordedTransfer.transition.live_snapshot.frontier.val[l.val]!) = _
  have he : PV_RunJoin_RecordedTransfer.transition.live_snapshot.frontier =
      PV_RunJoin_FixtureArguments.snapshot.frontier := rfl
  rw [he]
  funext i
  exact PV_RunJoin_FixtureCorrespondence20.frontier l i
#print axioms transfer

theorem withdrawal : PV_RunJoin_PublicCore21.withdrawal.snapshotFrontier = (fixturePublic true).snapshotFrontier := by
  funext l
  change digK (K := M) (PV_RunJoin_RecordedWithdrawal.transition.live_snapshot.frontier.val[l.val]!) = _
  have he : PV_RunJoin_RecordedWithdrawal.transition.live_snapshot.frontier =
      PV_RunJoin_FixtureArguments.snapshot.frontier := rfl
  rw [he]
  funext i
  exact PV_RunJoin_FixtureCorrespondence20.frontier l i
#print axioms withdrawal
end R1Z.PV_RunJoin_PublicSnapshot21
