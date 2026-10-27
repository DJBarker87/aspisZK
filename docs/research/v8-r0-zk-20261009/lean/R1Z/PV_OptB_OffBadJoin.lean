import R1Z.PV_OptB_OffBad
import R1Z.PV_OptB_DeployedSignal
set_option autoImplicit false
namespace R1Z.PV_OptB_OffBadJoin
open Aeneas Aeneas.Std Result ProverCommitRetry34
open PV_OptB_ControlRelation PV_OptB_ControlObservation PV_RunJoin_UnifiedRetry
variable [ProverRwFull.ExternalTypes] [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]
variable {N L C W Public World Coins E Event : Type}

/-- Source P obligation localized to the two good runs at common coordinates.
This is not an instance and is not a field of the capped trust list. -/
def Steps (pub : W → Public)
    (bad : W → World → Coins → Prop)
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : W → Body (State N L C))
    (R : State N L C → State N L C → Prop) : Prop :=
  ∀ w u, pub w = pub u → ∀ os coins, ¬ bad w os coins → ¬ bad u os coins →
    ∀ i s t, i < 8 → R s t → Related R
      (attempt account (body w) i s) (attempt account (body u) i t)

/-- Existing retry synchronization, now requiring source steps only off the
already charged events. No claim that the native body meets `Steps`. -/
theorem related_off_bad
    (pub : W → Public) (bad : W → World → Coins → Prop)
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : W → Body (State N L C))
    (R : State N L C → State N L C → Prop)
    (steps : Steps pub bad account body R)
    (w u : W) (same : pub w = pub u) (os : World) (coins : Coins)
    (hw : ¬ bad w os coins) (hu : ¬ bad u os coins)
    (s t : State N L C) (initial : R s t) :
    Related R (client account (body w) s) (client account (body u) t) :=
  PV_OptB_RunJoinControl.client_related account (body w) (body u) R
    (steps w u same os coins hw hu) s t initial
#print axioms related_off_bad
theorem observations_off_bad
    (pub : W → Public) (bad : W → World → Coins → Prop)
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : W → Body (State N L C))
    (R : State N L C → State N L C → Prop)
    (steps : Steps pub bad account body R) (read : State N L C → E)
    (preserved : ∀ s t, R s t → read s = read t)
    (w u : W) (same : pub w = pub u) (os : World) (coins : Coins)
    (hw : ¬ bad w os coins) (hu : ¬ bad u os coins)
    (s t : State N L C) (initial : R s t) :
    observation read (client account (body w) s) = observation read (client account (body u) t) :=
  observation_equal R read read preserved _ _
    (related_off_bad pub bad account body R steps w u same os coins hw hu s t initial)

#print axioms observations_off_bad
theorem independent_off_bad
    (pub : W → Public) (bad : W → World → Coins → Prop)
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : W → Body (State N L C))
    (initial : World → Coins → State N L C)
    (R : State N L C → State N L C → Prop)
    (steps : Steps pub bad account body R)
    (initial_related : ∀ os coins, R (initial os coins) (initial os coins))
    (read : State N L C → E) (preserved : ∀ s t, R s t → read s = read t)
    (decode : Result E → Option Event) :
    PV_OptB_Factorization.IndependentOffBad pub
      (fun w os coins => decode (observation read (client account (body w) (initial os coins)))) bad := by
  intro w u same os coins hw hu
  exact congrArg decode (observations_off_bad pub bad account body R steps read preserved
    w u same os coins hw hu (initial os coins) (initial os coins) (initial_related os coins))

#print axioms independent_off_bad
theorem decoder_off_bad
    (pub : W → Public) (bad : W → World → Coins → Prop)
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : W → Body (State N L C))
    (initial : World → Coins → State N L C)
    (R : State N L C → State N L C → Prop)
    (steps : Steps pub bad account body R)
    (initial_related : ∀ os coins, R (initial os coins) (initial os coins))
    (read : State N L C → E) (preserved : ∀ s t, R s t → read s = read t)
    (decode : Result E → Option Event) :
    ∃ decoder : Public → World → Coins → Option Event,
      ∀ w os coins, ¬ bad w os coins →
        decode (observation read (client account (body w) (initial os coins))) = decoder (pub w) os coins :=
  PV_OptB_Factorization.decoder_of_off_bad pub _ bad
    (independent_off_bad pub bad account body initial R steps initial_related read preserved decode)

#print axioms decoder_off_bad
end R1Z.PV_OptB_OffBadJoin
