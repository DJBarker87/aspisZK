import Lean
import NGK_NFR_RawInverseHelpers

set_option autoImplicit false
noncomputable section
namespace NGK_NFR_RawInverseValidator
open Aeneas Aeneas.Std Result WP AspisR1TerminalDecoder
open AspisR1.S2K NGK_NFO_ResultLayout

@[local step] theorem encoder (value : pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
    pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 value ⦃ _ => True ⦄ := by
  obtain ⟨result,run⟩ := AspisS6NativeAfterstateCodec.encode_total value
  rw [run,WP.spec_ok]
  trivial
#print axioms encoder


@[local step] theorem map {T : Type} (r : core.result.Result T pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) :
    AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_forest_terminal.validate_result.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1 r () ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases r <;> exact ⟨_,rfl,trivial⟩
#print axioms map

@[local step] theorem map_1 {T : Type} (r : core.result.Result T pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
    AspisR1TerminalDecoder.core.result.Result.map_err pool_v1.pair_forest_terminal.validate_result.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1 r () ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases r <;> exact ⟨_,rfl,trivial⟩
#print axioms map_1
@[step] theorem validate (value : Output) :
    pool_v1.pair_forest_terminal.validate_result value ⦃ _ => True ⦄ := by
  unfold pool_v1.pair_forest_terminal.validate_result
  step*
#print axioms validate
end NGK_NFR_RawInverseValidator

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
