import R1Z.PV_OptB_OffBad
import R1Z.PV_OptB_FirstWorldSignal
set_option autoImplicit false
namespace R1Z.PV_OptB_FirstFailureOffBad
open Aeneas Aeneas.Std Result ProverRwRngCaller
open R0Z R0Z.JointView R0Z.FsStatement
local instance : NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable [ProverRwFull.ExternalTypes]
variable {CommitHandle Aux Coins N L C Event : Type}
local notation "K" => PrivacyR1AcctBasis.K

/-- Complete result equality on the already proved first-draw fault family.
No body-step hypothesis is used here. Later reached failures remain open. -/
theorem execute_pair
    (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L C)
    (h : HonestProver K) (x : Statement K CommitHandle)
    (r : PV_RunJoin_Deployed.World runtime)
    (fault : PV_OptB_RuntimeFirstDraw.FirstDrawFailure runtime r) (w u : h.Instance) :
    PV_RunJoin_Deployed.execute runtime h x w r = PV_RunJoin_Deployed.execute runtime h x u r :=
  (PV_OptB_RuntimeFirstDraw.execute_failure runtime r fault h x w).trans
    (PV_OptB_RuntimeFirstDraw.execute_failure runtime r fault h x u).symm

#print axioms execute_pair
theorem signal_pair
    (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L C)
    (h : HonestProver K) (x : Statement K CommitHandle)
    (r : PV_RunJoin_Deployed.World runtime)
    (fault : PV_OptB_RuntimeFirstDraw.FirstDrawFailure runtime r) (w u : h.Instance)
    (decode : Result (PV_RunJoin_Deployed.Output N L C) → Option Event) :
    decode (PV_RunJoin_Deployed.execute runtime h x w r) =
      decode (PV_RunJoin_Deployed.execute runtime h x u r) :=
  congrArg decode (execute_pair runtime h x r fault w u)

#print axioms signal_pair
theorem independent_off_bad_on_first_failures
    (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L C)
    (h : HonestProver K) (x : Statement K CommitHandle)
    (decode : Result (PV_RunJoin_Deployed.Output N L C) → Option Event)
    (bad : h.Instance →
      (Σ r : PV_RunJoin_Deployed.World runtime, PV_OptB_RuntimeFirstDraw.FirstDrawFailure runtime r) → Unit → Prop) :
    PV_OptB_Factorization.IndependentOffBad h.public
      (fun w (r : Σ r : PV_RunJoin_Deployed.World runtime, PV_OptB_RuntimeFirstDraw.FirstDrawFailure runtime r)
        (_ : Unit) => decode (PV_RunJoin_Deployed.execute runtime h x w r.1)) bad :=
  PV_OptB_Factorization.independent_implies_off_bad h.public _ bad
    (PV_OptB_FirstWorldSignal.independent_on_first_failures runtime h x decode)

#print axioms independent_off_bad_on_first_failures
end R1Z.PV_OptB_FirstFailureOffBad
