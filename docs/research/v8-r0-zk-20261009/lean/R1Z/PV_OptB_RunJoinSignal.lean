import R1Z.PV_OptB_RunJoinControl
import R1Z.PV_OptB_Factorization
set_option autoImplicit false
namespace R1Z.PV_OptB_RunJoinSignal
open Aeneas Aeneas.Std Result ProverCommitRetry34 PV_OptB_ControlRelation
open PV_RunJoin_UnifiedRetry PV_OptB_ControlObservation
variable [ProverRwFull.ExternalTypes] [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]
variable {N L C W Public World Coins E Event : Type}

theorem independent
    (pub : W → Public) (account : ProverRwEffectCallback.Account (State N L C))
    (body : W → Body (State N L C)) (initial : World → Coins → State N L C)
    (R : State N L C → State N L C → Prop)
    (read : State N L C → E) (decode : Result E → Option Event)
    (initial_related : ∀ os coins, R (initial os coins) (initial os coins))
    (read_related : ∀ s t, R s t → read s = read t)
    (step : ∀ w u, pub w = pub u → ∀ i s t, i < 8 → R s t → Related R
      (attempt account (body w) i s) (attempt account (body u) i t)) :
    PV_OptB_Factorization.Independent pub
      (fun w os coins => decode (observation read (client account (body w) (initial os coins)))) := by
  intro w u same os coins
  apply congrArg decode
  exact observation_equal R read read read_related _ _
    (PV_OptB_RunJoinControl.client_related account (body w) (body u) R (step w u same)
      (initial os coins) (initial os coins) (initial_related os coins))

#print axioms independent
end R1Z.PV_OptB_RunJoinSignal
