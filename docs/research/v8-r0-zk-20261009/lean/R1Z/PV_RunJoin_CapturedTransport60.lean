import R1Z.PV_RunJoin_CaptureFactorRelation60
import R1Z.PV_RunJoin_NativeResult55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CapturedTransport60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_ResultRelation55
open PV_RunJoin_CaptureFactorRelation60 (resume)
variable [ExternalTypes] [ExternalFuns]

theorem complete {A B T : Type} (R : A → B → Prop)
    (f : Phase → Result (core.result.Result A verifier.Error))
    (g : Phase → Result (core.result.Result B verifier.Error))
    (beforeResult : Result (core.result.Result (Phase × prover.MaskedFixtureAudit) verifier.Error × T))
    (step : ∀ p audit next, beforeResult=ok (.Ok (p,audit),next) → Rel (CoreRel R) (f p) (g p)) :
    Rel (PV_RunJoin_NativeResult55.Output R) (resume f beforeResult) (resume g beforeResult) := by
  cases hp : beforeResult with
  | fail e => exact .fail e
  | div => exact .div
  | ok pair =>
    rcases pair with ⟨status,next⟩
    cases status with
    | Err e => exact .ok ⟨.err e,rfl⟩
    | Ok pair =>
      rcases pair with ⟨p,audit⟩
      have h := step p audit next hp
      cases h with
      | fail e => exact .fail e
      | div => exact .div
      | ok h => cases h with
        | err e => exact .ok ⟨.err e,rfl⟩
        | ok h => exact .ok ⟨.ok ⟨h,rfl⟩,rfl⟩

#print axioms complete
end R1Z.PV_RunJoin_CapturedTransport60
