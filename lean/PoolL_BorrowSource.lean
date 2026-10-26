import PoolL_LengthSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_BorrowSource
open Aeneas Aeneas.Std Result PoolM_NativeCancelSource
/- AENEAS007: length disjunct or explicit borrowed-data cut; actual SDK association remains open. -/
def PoolL_borrow_length
  (data : core.result.Result (Slice Std.U8) solana_program_error.ProgramError)
  (exact_bytes : Std.Usize) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch data
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    PoolL_LengthSource.lengthPrefix val exact_bytes
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame solana_program_error.ProgramError) residual
end AspisR1.PoolL_BorrowSource
end
