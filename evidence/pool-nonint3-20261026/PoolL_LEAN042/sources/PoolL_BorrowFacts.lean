import PoolL_BorrowSource
import PoolL_LengthAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_BorrowFacts
open Aeneas Aeneas.Std Result PoolL_BorrowSource
abbrev Error := AdapterRw.solana_program_error.ProgramError

theorem success (data : Slice U8) (n : Usize) :
    PoolL_borrow_length (.Ok data) n = PoolL_LengthSource.lengthPrefix data n := by
  simp [PoolL_borrow_length,core.result.Result.Insts.CoreOpsTry.branch]
theorem error (err : Error) (n : Usize) :
    PoolL_borrow_length (.Err err) n = ok (.Err err) := by
  simp [PoolL_borrow_length,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
theorem accepted (data : core.result.Result (Slice U8) Error) (n : Usize) :
    PoolL_borrow_length data n = ok (.Ok ()) ↔
      ∃ bytes, data = .Ok bytes ∧ bytes.val.length = n.val := by
  cases data with
  | Ok bytes => rw [success,PoolL_LengthAccepted.accepted]; simp
  | Err err => rw [error]; simp
#print axioms success
#print axioms error
#print axioms accepted
end AspisR1.PoolL_BorrowFacts
end
