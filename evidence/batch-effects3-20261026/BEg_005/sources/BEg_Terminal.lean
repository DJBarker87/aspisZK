import BEg_Observation
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEg_Terminal
open Aeneas Aeneas.Std Result SdkC_Source
open BEg_Observation

/-- Canonical rejection is only a proof observation, never an installed decoder
or a replacement for shipped source. -/
def canonical {A E : Type} : core.result.Result A E → Result (core.result.Result A E)
  | .Ok a => .ok (.Ok a)
  | .Err _ => .fail .panic

def terminal {A E : Type} (code : Code (core.result.Result A E)) :
    Code (core.result.Result A E) :=
  code >>= fun value => CheckpointBytes5Effect.liftResult (canonical value)

/-- A terminal error-kind change preserves the complete successful result,
all carrier effects, and the exact ordered attempted log on every outcome.
No assumption that reads preserve the carrier is made. -/
theorem transport {S A E : Type} (call : Parts → S → Result Digest × S)
    (code : Code (core.result.Result A E)) (state : S) (before : Log) :
    observe (BEf_Carrier.run call (terminal code) state before) =
      observe (BEf_Carrier.run call code state before) := by
  rw [terminal,BEf_Bind.run]
  cases h : BEf_Carrier.run call code state before with
  | mk value effects =>
    cases value with
    | fail e => rfl
    | div => rfl
    | ok value => cases value <;> rfl

theorem effects {S A E : Type} (call : Parts → S → Result Digest × S)
    (code : Code (core.result.Result A E)) (state : S) (before : Log) :
    (BEf_Carrier.run call (terminal code) state before).2 =
      (BEf_Carrier.run call code state before).2 :=
  congrArg (fun out : Option A × S × Log => out.2) (transport call code state before)

theorem accepted {S A E : Type} (call : Parts → S → Result Digest × S)
    (code : Code (core.result.Result A E)) (state : S) (before : Log) (a : A) :
    (BEf_Carrier.run call (terminal code) state before).1 = .ok (.Ok a) ↔
      (BEf_Carrier.run call code state before).1 = .ok (.Ok a) := by
  rw [←accepted_iff,←accepted_iff]
  have same := congrArg (fun out : Option A × S × Log => out.1) (transport call code state before)
  change BEg_Observation.accepted _ = some a ↔ BEg_Observation.accepted _ = some a
  change BEg_Observation.accepted _ = BEg_Observation.accepted _ at same
  rw [same]

#print axioms transport
#print axioms effects
#print axioms accepted
end AspisR1.BEg_Terminal
end
