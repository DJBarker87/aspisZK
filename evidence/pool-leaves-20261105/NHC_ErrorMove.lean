import NGK_COMBINED_IMPORT
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NHC_ErrorMove
/-- Generic residual propagation includes every ProgramError payload. No numeric
encoding or finite String bound is introduced. This is a model law only. -/
theorem propagate {R E : Type} (e : E) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      R (core.convert.FromSame E) (.Err e) = ok (.Err e) := by
  rfl
#print axioms propagate

theorem borsh (s : String) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame AdapterRw.solana_program_error.ProgramError)
      (.Err (AdapterRw.solana_program_error.ProgramError.BorshIoError s)) =
    ok (.Err (AdapterRw.solana_program_error.ProgramError.BorshIoError s)) := by
  exact propagate _
#print axioms borsh
end NHC_ErrorMove
