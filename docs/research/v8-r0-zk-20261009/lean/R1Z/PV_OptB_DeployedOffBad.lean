import R1Z.PV_OptB_OffBadJoin
set_option autoImplicit false
namespace R1Z.PV_OptB_DeployedOffBad
open Aeneas Aeneas.Std Result ProverRwRngCaller
open R0Z R0Z.JointView R0Z.FsStatement
open PV_RunJoin_UnifiedRetry PV_OptB_ControlObservation
local instance : NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable [ProverRwFull.ExternalTypes]
variable {CommitHandle Aux Coins N L C E Event : Type}
local notation "K" => PrivacyR1AcctBasis.K

/-- The actual `execute`, conditional on a native off-bad body-step proof.
The existing `Runtime.body` and all world fields are used read-only. No
native instance of `Steps` is installed by this theorem. -/
theorem conditional_off_bad
    (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L C)
    (h : HonestProver K) (x : Statement K CommitHandle)
    (bad : h.Instance → PV_RunJoin_Deployed.World runtime → Unit → Prop)
    (R : State N L C → State N L C → Prop)
    (read : State N L C → E) (decode : Result E → Option Event)
    (initial : ∀ r : PV_RunJoin_Deployed.World runtime, R r.state r.state)
    (preserved : ∀ s t, R s t → read s = read t)
    (step : PV_OptB_OffBadJoin.Steps h.public bad runtime.account (runtime.body h x) R) :
    PV_OptB_Factorization.IndependentOffBad h.public
      (fun w (r : PV_RunJoin_Deployed.World runtime) (_ : Unit) =>
        decode (observation read (PV_RunJoin_Deployed.execute runtime h x w r))) bad := by
  exact PV_OptB_OffBadJoin.independent_off_bad h.public bad runtime.account (runtime.body h x)
    (fun (r : PV_RunJoin_Deployed.World runtime) (_ : Unit) => r.state)
    R step (fun r _ => initial r) read preserved decode

#print axioms conditional_off_bad
end R1Z.PV_OptB_DeployedOffBad
