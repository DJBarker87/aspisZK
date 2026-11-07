import NMX_R3_RegistryPrefix0
import LIBB_PoolLib
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPolicy
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
abbrev Output := core.result.Result Unit solana_program_error.ProgramError

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (p : aspis_statement.pool_v1.format.VerifierPolicyV1) (next : Program Output) (f : RSL.RS Unit)
 (hn : RSL.Spec.map (reply id) (eval next) = f) :
 RSL.Spec.map (reply id) (eval (NMX_R3_RegistryPrefix0.policyTail (NMX_R3_RegistryOps.install base D env) p next)) =
 RSL.RS.seq (RSL.RS.check (!LIBB_PoolLib.library.validatePolicy (policy p)) .invalidAccountData) f := by
 let out := LIBB_ResultTotal.value (NHY_PolicyModel.policy p) (LIBB_PolicyValue.total p)
 have he : NHY_PolicyModel.policy p = Result.ok out := LIBB_ResultTotal.equation _ _
 have hv : LIBB_PolicyValue.isOk out = LIBB_PoolLib.library.validatePolicy (policy p) := by
  have h := LIBB_PolicyValue.native p
  rw [he] at h
  exact Result.ok.inj h
 unfold NMX_R3_RegistryPrefix0.policyTail
 rw [eval_bind,eval_scalar]
 change RSL.Spec.map (reply id) (RSL.Spec.bind (scalarSpec (NHY_PolicyModel.policy p))
  (fun r => eval (NMX_R3_RegistryProtocols.formatTail
   r1_pool_adapter.owned.authenticate_invariant_release_registry.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1FormatErrorProgramError
   () r (fun _ => next)))) = _
 conv_lhs => rw [he]
 simp only [scalarSpec,RSL.Spec.bind_pure]
 rw [NMX_R3_RegistryProtocols.eval_format
  r1_pool_adapter.owned.authenticate_invariant_release_registry.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1FormatErrorProgramError
  () (fun _ => rfl) out (fun _ => next)]
 rw [←hv]
 cases out with
 | Ok u =>
  simpa only [LIBB_PolicyValue.isOk,Bool.not_true,Bool.false_eq_true,↓reduceIte,
   RSL.RS.check,RSL.RS.seq,RSL.RS.bind_pure] using hn
 | Err e =>
  simp only [LIBB_PolicyValue.isOk,Bool.not_false,↓reduceIte,
   RSL.RS.check,RSL.RS.seq,RSL.RS.bind_throw,NMX_R3_RegistryEffectLaws.map_pure,reply]
  <;> rfl
#print axioms fold
end NMX_R3_RegistryPolicy
end
