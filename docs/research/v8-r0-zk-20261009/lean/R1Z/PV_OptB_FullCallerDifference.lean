import R1Z.PV_OptB_SourceEntry
import R1Z.PV_OptB_SourceConditionalDifference
set_option autoImplicit false
namespace R1Z.PV_OptB_FullCallerDifference
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

abbrev entropy {S : Type} (account : ProverRwEffectCallback.Account S) : Entropy S :=
  RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError account

/-- Full extracted proof-account entry, conditional on its missing body
facts. No replacement retry body and no altered observer are installed. -/
theorem conditional {S : Type} (account : ProverRwEffectCallback.Account S) (pub : Pub)
    (left right : Compiled) (hash : Hash) (store leftStore rightStore : Store)
    (state next final : S) (secret : Secret)
    (variant : core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant .S2 .S2 = .ok false)
    (first : (entropy account).call_mut state 0#usize = .ok (.Ok secret,next))
    (second : (entropy account).call_mut next 1#usize = .ok (.Err .Entropy,final))
    (leftBody : prover.prove_masked_attempt pub left .S2 hash secret store =
      .ok (.Err .Semantic,leftStore))
    (rightBody : prover.prove_masked_attempt pub right .S2 hash secret store =
      .ok (.Err .Rejected,rightStore)) :
    RealR1_client.prove_for_proof_accounts account pub left hash store state ≠
      RealR1_client.prove_for_proof_accounts account pub right hash store state := by
  rw [PV_OptB_SourceEntry.entry account pub left hash store state variant,
    PV_OptB_SourceEntry.entry account pub right hash store state variant]
  exact PV_OptB_SourceConditionalDifference.semantic_vs_second_entropy
    (entropy account) pub left right hash store leftStore rightStore state next final secret
    first second leftBody rightBody

#print axioms conditional
end R1Z.PV_OptB_FullCallerDifference
