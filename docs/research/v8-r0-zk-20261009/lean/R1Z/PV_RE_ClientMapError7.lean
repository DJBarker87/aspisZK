import R1Z.PV_RE_AttemptMapError7
import R1Z.PV_RE_ClientContext7
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientMapError7
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep PV_RE_PublicPrefix6
variable [ExternalTypes]
theorem client_to_maperror {C : Type} (D : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets)
    (guard : D.op233 .S2 .S2 = .ok true)
    (entropy_prefix : (EntropyWrapper D entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1))
    (bytes : alloc.vec.Vec U8)
    (serialization : D.op226 pub = .ok (.Ok bytes))
 :
    ∃ next, @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state =
      (D.op12
        prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
        (.Ok bytes) () >>= next) := by
  apply PV_RE_ClientAttempt7.lift_prefix D entropy pub compiled hash store state state1 secret
    guard entropy_prefix (D.op12
        prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
        (.Ok bytes) ())
  exact PV_RE_AttemptMapError7.attempt_to_maperror D pub compiled .S2 hash secret store bytes serialization
#print axioms client_to_maperror
end R1Z.PV_RE_ClientMapError7
