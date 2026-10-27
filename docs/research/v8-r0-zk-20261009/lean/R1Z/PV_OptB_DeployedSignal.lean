import R1Z.PV_OptB_RunJoinSignal
import R1Z.PV_RunJoin_Deployed
set_option autoImplicit false
namespace R1Z.PV_OptB_DeployedSignal
open Aeneas Aeneas.Std Result ProverRwRngCaller
open R0Z R0Z.JointView R0Z.FsStatement
open PV_RunJoin_UnifiedRetry PV_OptB_ControlRelation PV_OptB_ControlObservation
local instance : NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable [ProverRwFull.ExternalTypes]
variable {CommitHandle Aux Coins N L C E Event : Type}
local notation "K" => PrivacyR1AcctBasis.K

/-- Sufficient P obligation for the exact deployed effect interpreter. It
is deliberately still a hypothesis: no native body synchronization instance
has been built, and no endpoint premise has been removed. -/
theorem conditional_independence
    (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L C)
    (h : HonestProver K) (x : Statement K CommitHandle)
    (R : State N L C → State N L C → Prop)
    (read : State N L C → E) (decode : Result E → Option Event)
    (initial : ∀ r : PV_RunJoin_Deployed.World runtime, R r.state r.state)
    (preserved : ∀ s t, R s t → read s = read t)
    (step : ∀ w u : h.Instance, h.public w = h.public u → ∀ i s t, i < 8 → R s t →
      Related R (attempt runtime.account (runtime.body h x w) i s)
        (attempt runtime.account (runtime.body h x u) i t)) :
    PV_OptB_Factorization.Independent h.public
      (fun w (r : PV_RunJoin_Deployed.World runtime) (_ : Unit) =>
        decode (observation read (PV_RunJoin_Deployed.execute runtime h x w r))) := by
  exact PV_OptB_RunJoinSignal.independent h.public runtime.account (runtime.body h x)
    (fun (r : PV_RunJoin_Deployed.World runtime) (_ : Unit) => r.state)
    R read decode (fun r _ => initial r) preserved step

#print axioms conditional_independence
end R1Z.PV_OptB_DeployedSignal
