import R1Z.PV_RunJoin_HonestConsumer26
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_HonestFixtures26
open R0P R0Z.ZkStatement R0Z.HonestValidity PV_RunJoin_HonestIdentification26
local notation "K" => PrivacyR1AcctBasis.K
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P

def transfer : Honest (K := K) :=
  ⟨PV_RunJoin_AdmittedCarrier23.transfer, PV_RunJoin_ConsumerBoundary25.transfer_honest⟩
def withdrawal : Honest (K := K) :=
  ⟨PV_RunJoin_AdmittedCarrier23.withdrawal, PV_RunJoin_ConsumerBoundary25.withdrawal_honest⟩

def statement (i : Honest (K := K)) : Statement K Unit := (source_honest.public i, ())

/-- Non-vacuity is constructive: both original fixtures are in the carrier. -/
theorem inhabited : Nonempty (Honest (K := K)) := ⟨transfer⟩
#print axioms inhabited

theorem transfer_identified :
    source_honest.public transfer = BuilderSource.prover.public (target transfer) ∧
    source_honest.build transfer = BuilderSource.prover.build (target transfer) :=
  ⟨public_eq transfer, build_eq transfer⟩
#print axioms transfer_identified

theorem withdrawal_identified :
    source_honest.public withdrawal = BuilderSource.prover.public (target withdrawal) ∧
    source_honest.build withdrawal = BuilderSource.prover.build (target withdrawal) :=
  ⟨public_eq withdrawal, build_eq withdrawal⟩
#print axioms withdrawal_identified

/-- V047 non-vacuity on the exact public of either honest fixture. -/
theorem fibre (i : Honest (K := K)) :
    (∃ w : (source_honest (K := K)).Instance, source_honest.public w = (statement i).1) ∧
    (∃ p : BuilderCanonical.Instance (K := K),
      BuilderSource.prover.public p = (statement i).1 ∧
      source_honest.build i = BuilderSource.prover.build p) :=
  ⟨⟨i,rfl⟩,⟨target i,PV_RunJoin_HonestConsumer26.canonical_fibre (statement i) i rfl⟩⟩
#print axioms fibre

theorem transfer_fibre := fibre transfer
#print axioms transfer_fibre

theorem withdrawal_fibre := fibre withdrawal
#print axioms withdrawal_fibre

/-- Both public fibres can actually invoke the unchanged consumer. -/
theorem fixture_consumers {F : Subfield K} (B : PackBasis F) :
    (PublicBase F (statement transfer).1 ∧
      BuilderSoundOn (source_honest (K := K)) B (statement transfer)) ∧
    (PublicBase F (statement withdrawal).1 ∧
      BuilderSoundOn (source_honest (K := K)) B (statement withdrawal)) :=
  ⟨PV_RunJoin_HonestConsumer26.at_honest_input B _ transfer rfl,
   PV_RunJoin_HonestConsumer26.at_honest_input B _ withdrawal rfl⟩
#print axioms fixture_consumers
end R1Z.PV_RunJoin_HonestFixtures26
