import R1Z.PV_RunJoin_FixtureFibres
import R1Z.PV_RunJoin_TransferSentinel
import R1Z.PrivacyR1AcctBasis

/-! Concrete nonempty mathematical fibres at the headline field. Native
public-record/byte association remains explicit, one equation per fixture. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalFixtures
open R1J.SpendWitnessMap PV_RunJoin_FixtureRecords
abbrev Scalar := PrivacyR1AcctBasis.K

local instance : CharP Scalar 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) Scalar).injective
    AspisCircleGroupOrder.P

def transfer : BuilderCanonical.Instance (K := Scalar) :=
  PV_RunJoin_FixtureFibres.transfer PV_RunJoin_TransferSentinel.nonzero

def withdrawal : BuilderCanonical.Instance (K := Scalar) := PV_RunJoin_FixtureFibres.withdrawal

theorem transfer_public :
    (BuilderSource.prover (K := Scalar)).public transfer = mapPub (fixturePublic false) := rfl

theorem withdrawal_public :
    (BuilderSource.prover (K := Scalar)).public withdrawal = mapPub (fixturePublic true) := rfl

/-- The two remaining V047 associations. The transfer-sentinel field in the
predecessor FixturePremises is now proved, so it is not an input here. These
equations must be proved for the actual released public records. -/
structure Association {CommitHandle : Type}
    (transferX withdrawalX : R0Z.ZkStatement.Statement Scalar CommitHandle) : Prop where
  transfer_public_V047 : transferX.1 = mapPub (fixturePublic false)
  withdrawal_public_V047 : withdrawalX.1 = mapPub (fixturePublic true)

theorem predecessor_premises {CommitHandle : Type}
    {transferX withdrawalX : R0Z.ZkStatement.Statement Scalar CommitHandle}
    (association : Association transferX withdrawalX) :
    PV_RunJoin_FixtureFibres.FixturePremises transferX withdrawalX :=
  ⟨association.transfer_public_V047,association.withdrawal_public_V047,
    PV_RunJoin_TransferSentinel.nonzero⟩

theorem fibres {CommitHandle : Type}
    {transferX withdrawalX : R0Z.ZkStatement.Statement Scalar CommitHandle}
    (association : Association transferX withdrawalX) :
    (BuilderSource.prover (K := Scalar)).public transfer = transferX.1 ∧
      (BuilderSource.prover (K := Scalar)).public withdrawal = withdrawalX.1 :=
  ⟨transfer_public.trans association.transfer_public_V047.symm,
    withdrawal_public.trans association.withdrawal_public_V047.symm⟩

/-- Non-vacuity of these explicit mathematical fixture statements, for every
choice of handles. This does not identify handles or bytes with native output. -/
theorem mathematical_fibres {CommitHandle : Type} (transferHandle withdrawalHandle : CommitHandle) :
    let transferX : R0Z.ZkStatement.Statement Scalar CommitHandle := (mapPub (fixturePublic false),transferHandle)
    let withdrawalX : R0Z.ZkStatement.Statement Scalar CommitHandle := (mapPub (fixturePublic true),withdrawalHandle)
    ∃ wt ww : (BuilderSource.prover (K := Scalar)).Instance,
      (BuilderSource.prover (K := Scalar)).public wt = transferX.1 ∧
      (BuilderSource.prover (K := Scalar)).public ww = withdrawalX.1 :=
  ⟨transfer,withdrawal,transfer_public,withdrawal_public⟩

#print axioms transfer
#print axioms withdrawal
#print axioms transfer_public
#print axioms withdrawal_public
#print axioms predecessor_premises
#print axioms fibres
#print axioms mathematical_fibres
end R1Z.PV_RunJoin_CanonicalFixtures
