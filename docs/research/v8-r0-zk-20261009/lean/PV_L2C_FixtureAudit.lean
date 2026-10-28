import R1Z.PV_RunJoin_ConsumerBoundary25
set_option autoImplicit false
noncomputable section
namespace PV_L2C_FixtureAudit
open R1Z
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Non-vacuity of exactly the requested carrier, with no guard-success field. -/
theorem transfer : PV_RunJoin_ConsumerBoundary25.HonestInput (K:=K)
    PV_RunJoin_AdmittedCarrier23.transfer :=
  PV_RunJoin_ConsumerBoundary25.transfer_honest
#print axioms transfer

theorem withdrawal : PV_RunJoin_ConsumerBoundary25.HonestInput (K:=K)
    PV_RunJoin_AdmittedCarrier23.withdrawal :=
  PV_RunJoin_ConsumerBoundary25.withdrawal_honest
#print axioms withdrawal

theorem nonempty : ∃ i, PV_RunJoin_ConsumerBoundary25.HonestInput (K:=K) i :=
  ⟨_, transfer⟩
#print axioms nonempty
end PV_L2C_FixtureAudit
