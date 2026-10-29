import R1Z.PV_RunJoin_CaptureAudit60
import R1Z.PV_RunJoin_NativeBuildSource55
import R1Z.PV_RunJoin_NativeAuditSource55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CaptureSource60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_ActualProvenance60 (capture Produced)
variable [ExternalTypes] [ExternalFuns]

theorem complete {A T : Type} (f : Phase → Result (core.result.Result A verifier.Error))
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)
    (input : PV_RunJoin_NativePublication55.Input T) :
    PV_RunJoin_CaptureRelation60.Rel f
      (PV_RunJoin_NativeControl55.run f store input.public1 input.compiled .S2 input.hash
        input.context input.binding input.attempt input.store)
      (PV_RunJoin_NativeControl55.run capture store input.public1 input.compiled .S2 input.hash
        input.context input.binding input.attempt input.store) := by
  simp only [PV_RunJoin_NativeBuildSource55.complete,PV_RunJoin_NativeAuditSource55.complete]
  exact PV_RunJoin_CaptureAudit60.complete f store input.public1 input.compiled .S2 input.hash
    input.context input.binding input.attempt input.store

/-- The provenance obligation is discharged from the actual native prefix,
not supplied by a caller's assertion that a Phase is valid. -/
theorem produced {A T : Type} (f : Phase → Result (core.result.Result A verifier.Error))
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)
    (input : PV_RunJoin_NativePublication55.Input T)
    (a : A) (audit : prover.MaskedFixtureAudit) (next : T)
    (success : PV_RunJoin_NativeControl55.run f store input.public1 input.compiled .S2 input.hash
      input.context input.binding input.attempt input.store=ok (.Ok (a,audit),next)) :
    ∃ p, Produced p ∧ f p=ok (.Ok a) := by
  obtain ⟨p,hp,hf⟩ := complete f store input a audit next success
  exact ⟨p,⟨T,store,input,audit,next,hp⟩,hf⟩

#print axioms complete
#print axioms produced
end R1Z.PV_RunJoin_CaptureSource60
