import R1Z.ProverRwOuterPrefix
import R1Z.ProverRwRetryModel
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GenericSourceCaller
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

/-- Actual extracted public-prefix order, with its single generic store
parameter exposed. This is source staging, not a new shipped implementation. -/
def caller {S : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : Pub) (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (attempt : Secret) (s : S) : Result (core.result.Result Proof verifier.Error × S) := do
  let r ← aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub
  let r1 ← core.result.Result.map_err
    prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | .Continue val =>
    let (context,binding) ← ProverRwOuterPrefix.prepare val variant hash attempt.mask_nonce
    prover.prove_masked_with_attempt store pub compiled variant hash context binding attempt s
  | .Break residual =>
    let error ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Proof (core.convert.FromSame verifier.Error) residual
    .ok (error,s)

theorem source_eq (pub : Pub) (compiled : Compiled) (variant : transport.Variant)
    (hash : Hash) (attempt : Secret) (s : Store) :
    caller aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
      pub compiled variant hash attempt s =
    prover.prove_masked_attempt pub compiled variant hash attempt s := by
  rw [ProverRwOuterPrefix.attempt_factor]
  rfl

#print axioms source_eq
end R1Z.PV_RunJoin_GenericSourceCaller
