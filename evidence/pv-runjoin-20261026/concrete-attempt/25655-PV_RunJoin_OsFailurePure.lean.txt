import R1Z.PV_RunJoin_MapErrInstalled
import R1Z.PV_RunJoin_SourceFailureIndependence
import R1Z.ProverRwCallerBinding
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OsFailurePure
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel ProverRwEffectSource
variable [ExternalTypes]

def VariantIdentity (ops : ExternalFuns) : Prop := ops.op233 = ProverRwCallerBinding.variantEq

theorem client_map_error (ops : ExternalFuns) (identity : PV_RunJoin_MapErrInstalled.Identity ops)
    {S : Type} (account : ProverRwEffectCallback.Account S) (err : getrandom.error.Error) :
    letI : ExternalFuns := ops
    core.result.Result.map_err
      (RealR1_client.prove_for_proof_accounts.closure.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError account)
      (.Err (.Os err) : Status) () = .ok (.Err .Entropy) := by
  change @ExternalFuns.op12 _ ops = @ProverRwOuterMapErr.map_err at identity
  change ops.op12 _ _ _ = _
  rw [identity]
  rfl

theorem s2_ne (ops : ExternalFuns) (identity : VariantIdentity ops) :
    letI : ExternalFuns := ops
    core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant .S2 .S2 = .ok false := by
  letI : ExternalFuns := ops
  simp only [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    transport.Variant.Insts.CoreCmpPartialEqVariant,transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
    show ops.op233 = ProverRwCallerBinding.variantEq from identity,
    ProverRwCallerBinding.variantEq,bind_tc_ok,Bool.not_true]
  rfl

#print axioms client_map_error
#print axioms s2_ne
end R1Z.PV_RunJoin_OsFailurePure
