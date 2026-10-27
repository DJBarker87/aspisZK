import R1Z.PV_OptB_ControlObservation
import R1Z.PV_RunJoin_UnifiedRetry
set_option autoImplicit false
namespace R1Z.PV_OptB_RunJoinControl
open Aeneas Aeneas.Std Result ProverCommitRetry34 PV_OptB_ControlRelation
open PV_RunJoin_UnifiedRetry
variable [ProverRwFull.ExternalTypes] [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]
variable {N L C : Type}

/-- This is the actual UnifiedRetry client called by Deployed.execute. Its
per-step synchronization is an explicit P obligation, including reached
failure metadata retained in the changing world. -/
theorem client_related
    (account : ProverRwEffectCallback.Account (State N L C))
    (left right : Body (State N L C)) (R : State N L C → State N L C → Prop)
    (step : ∀ i s t, i < 8 → R s t → Related R
      (attempt account left i s) (attempt account right i t))
    (s t : State N L C) (initial : R s t) :
    Related R (client account left s) (client account right t) :=
  run_related R (attempt account left) (attempt account right) step 8 0 s t (by omega) initial

#print axioms client_related
end R1Z.PV_OptB_RunJoinControl
