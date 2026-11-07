import NMX_R3_RegistryEffectLaws
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryProtocols
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
abbrev Output := core.result.Result Unit solana_program_error.ProgramError

def tryTail {A : Type} (r : core.result.Result A solana_program_error.ProgramError)
 (next : A → Program Output) : Program Output := do
 let cf ← scalar (core.result.Result.Insts.CoreOpsTry.branch r)
 control cf next (fun residual => scalar
  (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
   Unit (core.convert.FromSame solana_program_error.ProgramError) residual))

def formatTail {A E O : Type}
 (inst : core.ops.function.FnOnce O E solana_program_error.ProgramError) (op : O)
 (r : core.result.Result A E) (next : A → Program Output) : Program Output := do
 let mapped ← scalar (AdapterRw.core.result.Result.map_err inst r op)
 tryTail mapped next

theorem eval_try {A : Type} (r : core.result.Result A solana_program_error.ProgramError)
 (next : A → Program Output) : eval (tryTail r next) =
 (match r with | .Ok a => eval (next a) | .Err e => RSL.Spec.pure (.Err e)) := by
 cases r <;> simp only [tryTail,eval_bind,eval_scalar,
  core.result.Result.Insts.CoreOpsTry.branch,scalarSpec,RSL.Spec.bind_pure,
  NMX_R3_RegistryProgram.control,eval_pure]
 <;> rfl

theorem eval_format {A E O : Type}
 (inst : core.ops.function.FnOnce O E solana_program_error.ProgramError) (op : O)
 (hc : ∀ e, inst.call_once op e = Result.ok .InvalidAccountData)
 (r : core.result.Result A E) (next : A → Program Output) : eval (formatTail inst op r next) =
 (match r with | .Ok a => eval (next a) | .Err _ => RSL.Spec.pure (.Err .InvalidAccountData)) := by
 cases r with
 | Ok a =>
  simp only [formatTail,AdapterRw.core.result.Result.map_err,eval_bind,eval_scalar,
   scalarSpec,RSL.Spec.bind_pure,eval_try]
 | Err e =>
  simp only [formatTail,AdapterRw.core.result.Result.map_err,hc,bind_tc_ok,eval_bind,eval_scalar,
   scalarSpec,RSL.Spec.bind_pure,eval_try]

#print axioms eval_try
#print axioms eval_format
end NMX_R3_RegistryProtocols
end
