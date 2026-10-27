import R1Z.PV_OptB_Factorization
import R1Z.PV_OptB_RuntimeFirstDraw
set_option autoImplicit false
namespace R1Z.PV_OptB_FirstWorldSignal
open Aeneas Aeneas.Std Result ProverRwRngCaller
open R0Z R0Z.JointView R0Z.FsStatement
local instance : NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable [ProverRwFull.ExternalTypes]
variable {CommitHandle Aux Coins N L C Event : Type}
local notation "K" => PrivacyR1AcctBasis.K

/-- All complete observations of the returned source result agree on the
existing exact first-draw-failure world family. This covers only that family. -/
theorem independent_on_first_failures
    (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L C)
    (h : HonestProver K) (x : Statement K CommitHandle)
    (decode : Result (PV_RunJoin_Deployed.Output N L C) → Option Event) :
    PV_OptB_Factorization.Independent h.public
      (fun w (r : Σ r : PV_RunJoin_Deployed.World runtime, PV_OptB_RuntimeFirstDraw.FirstDrawFailure runtime r)
          (_ : Unit) => decode (PV_RunJoin_Deployed.execute runtime h x w r.1)) := by
  intro w u _ r _
  apply congrArg decode
  exact (PV_OptB_RuntimeFirstDraw.execute_failure runtime r.1 r.2 h x w).trans
    (PV_OptB_RuntimeFirstDraw.execute_failure runtime r.1 r.2 h x u).symm

#print axioms independent_on_first_failures
end R1Z.PV_OptB_FirstWorldSignal
