import R1Z.PV_RunJoin_PublicExt21
import R1Z.PV_RunJoin_PublicScalars21
import R1Z.PV_RunJoin_PublicSnapshot21
import R1Z.PV_RunJoin_PublicRoots21
import R1Z.PV_RunJoin_PublicFrontier21
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalPublic21
open PV_RunJoin_PublicCore21 PV_RunJoin_PublicScalars21

theorem transfer : PV_Src_Public.canonicalPublic PV_RunJoin_RecordedTransfer.publicInput =
    PV_RunJoin_FixtureRecords.fixturePublic false :=
  PV_RunJoin_PublicExt21.source _ _ transfer_variant transfer_anchor transfer_nullifier
    transfer_asset transfer_recipient transfer_change transfer_amount transfer_index
    PV_RunJoin_PublicSnapshot21.transfer PV_RunJoin_PublicRoots21.transfer PV_RunJoin_PublicFrontier21.transfer
#print axioms transfer

theorem withdrawal : PV_Src_Public.canonicalPublic PV_RunJoin_RecordedWithdrawal.publicInput =
    PV_RunJoin_FixtureRecords.fixturePublic true :=
  PV_RunJoin_PublicExt21.source _ _ withdrawal_variant withdrawal_anchor withdrawal_nullifier
    withdrawal_asset withdrawal_recipient withdrawal_change withdrawal_amount withdrawal_index
    PV_RunJoin_PublicSnapshot21.withdrawal PV_RunJoin_PublicRoots21.withdrawal PV_RunJoin_PublicFrontier21.withdrawal
#print axioms withdrawal
end R1Z.PV_RunJoin_CanonicalPublic21
