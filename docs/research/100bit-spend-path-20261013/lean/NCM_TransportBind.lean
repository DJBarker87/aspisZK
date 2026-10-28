import NCE_CarrierEffects

set_option autoImplicit false
namespace AspisR1.NCM_TransportBind
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Ordered oracle-representation transport commutes with continuation.
This does not erase a failed prefix or introduce another execution. -/
theorem transport_bind {A B : Type} (program : Program Address Digest A)
    (next : A → Program Address Digest B) :
    transport (bind program next) = bind (transport program) (fun a => transport (next a)) := by
  induction program with
  | done a => rfl
  | ask input continuation ih =>
    simp only [AspisV8R19.OracleProgramOps.bind,transport]
    congr 1
    funext answer
    exact ih (AspisV8R19.SqueezeOracleBridge.encodeState answer)

/-- Value-level checked bind retains the original failure constructor. -/
theorem transport_checked {A B : Type} (result : Result A) (next : A → Run B) :
    transport (checked result next) =
      match result with
      | .ok a => transport (next a)
      | .fail e => .done (.fail e)
      | .div => .done .div := by
  cases result <;> rfl

#print axioms transport_bind
#print axioms transport_checked
end AspisR1.NCM_TransportBind
