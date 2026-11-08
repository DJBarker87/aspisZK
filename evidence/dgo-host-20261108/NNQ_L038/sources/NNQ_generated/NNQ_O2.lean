import NNQ_Account
import NNQ_ObserverConfig
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result

/- O2 statement quoted verbatim from DGP_HostDigest.lean section 3:
def O2 : Prop :=
  ∀ (m0 : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
    (env env' : RSL.Env) (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (a : SCE_Experiment.Adversary Bool) (Q : Nat),
    env.pda = env'.pda → env.clock = env'.clock → env.reservation = env'.reservation →
    NNH_RecordedCharge.recorder copy
        (IDa_Deployed.deployedConfiguration
          (NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m0 env) env) err r)
        err r hashv a Q =
      NNH_RecordedCharge.recorder copy
        (IDa_Deployed.deployedConfiguration
          (NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m0 env') env') err r)
        err r hashv a Q

-/
theorem o2 : AspisR1.DGP_HostDigest.O2 := by
  intro m0 copy err r env env' hashv a Q hp hc hr
  unfold NNH_RecordedCharge.recorder NNH_RecordedCharge.source
  rw [split m0 err r env env' hp hc hr]
  rw [account_withDigest, observer_withDigest]
#print axioms o2
end AspisR1.NNQ_HostDigest
end
