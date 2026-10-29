import R1Z.PV_RunJoin_AuditOrigin60
import R1Z.PV_RunJoin_NativeBuildSource55
import R1Z.PV_RunJoin_NativeAuditSource55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SourceOrigin60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_ActualProvenance60 (capture Produced)
open PV_RunJoin_ResultPost41 PV_RunJoin_BuildOrigin60
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) {T : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)
    (input : PV_RunJoin_NativePublication55.Input T) :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    Post (fun pair => match pair.1 with | .Err _ => True | .Ok (p,_) => Origin p)
      (PV_RunJoin_NativeControl55.run capture store input.public1 input.compiled .S2 input.hash
        input.context input.binding input.attempt input.store) := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  simp only [PV_RunJoin_NativeBuildSource55.complete,PV_RunJoin_NativeAuditSource55.complete]
  exact PV_RunJoin_AuditOrigin60.complete ops store input.public1 input.compiled input.hash
    input.context input.binding input.attempt input.store

theorem produced (ops : ExternalFuns) :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    ∀ p, Produced p → Origin p := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  intro p hp
  obtain ⟨T,store,input,audit,next,hp⟩ := hp
  have h := complete ops store input
  rw [hp] at h
  exact h

#print axioms complete
#print axioms produced
end R1Z.PV_RunJoin_SourceOrigin60
