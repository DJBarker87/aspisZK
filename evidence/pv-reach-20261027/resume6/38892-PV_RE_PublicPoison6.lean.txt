import R1Z.PV_RE_PublicPrefix6
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_PublicPoison6
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep PV_RE_PublicPrefix6
variable [ExternalTypes]

def poison226 (D : ExternalFuns) (e : Error) : ExternalFuns :=
  {D with op226 := fun _ => .fail e}

/-- The entropy prefix precedes op226 and does not use that dictionary field.
This is a symbolic equality on the original extracted closure and fixed-point
body; no concrete entropy iteration or fixture run is evaluated. -/
theorem entropy_transport {C : Type} (D : ExternalFuns) (e : Error)
    (entropy : RawEntropy C) (state : C) (k : Usize) :
    (EntropyWrapper (poison226 D e) entropy).call_mut state k =
      (EntropyWrapper D entropy).call_mut state k := by
  rfl

/-- Poisoning is transported across the actual successful variant and entropy
prefixes, then absorbed at the source's first public serialization call. -/
theorem poisoned_client_failure {C : Type} (D : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets)
    (guard : D.op233 .S2 .S2 = .ok true)
    (entropy_prefix : (EntropyWrapper D entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1)) (e : Error) :
    @RealR1_client.prove_for_proof_accounts _ (poison226 D e) C
      entropy pub compiled hash store state = .fail e := by
  apply client_public_failure (poison226 D e) entropy pub compiled hash store state state1 secret
  · exact guard
  · rw [entropy_transport]
    exact entropy_prefix
  · rfl

/-- A successful original execution with these actual prefixes distinguishes
op226 poisoning. This is a conditional lower bound, not a complete reached set. -/
theorem success_distinguishes {C : Type} (D : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets)
    (guard : D.op233 .S2 .S2 = .ok true)
    (entropy_prefix : (EntropyWrapper D entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1)) (e : Error)
    (v : (core.result.Result prover.RetriedProof verifier.Error) × Store)
    (success : @RealR1_client.prove_for_proof_accounts _ D C
      entropy pub compiled hash store state = .ok v) :
    @RealR1_client.prove_for_proof_accounts _ (poison226 D e) C
      entropy pub compiled hash store state ≠
    @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state := by
  rw [poisoned_client_failure D entropy pub compiled hash store state state1 secret guard entropy_prefix,
    success]
  intro h
  cases h

#print axioms poison226
#print axioms entropy_transport
#print axioms poisoned_client_failure
#print axioms success_distinguishes
end R1Z.PV_RE_PublicPoison6
