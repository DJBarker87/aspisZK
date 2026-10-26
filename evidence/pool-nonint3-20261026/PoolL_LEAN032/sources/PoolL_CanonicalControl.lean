import PoolL_CanonicalSource
import PoolL_ProgramControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_CanonicalControl
open Aeneas Aeneas.Std Result PoolL_CanonicalSource PoolL_ProgramControl
local instance : DecidableEq Key := Classical.decEq _
theorem control (a : Account) (id : Key) :
    PoolL_canonical_header a id =
      (if a.owner ≠ id then ok (.Err AdapterRw.solana_program_error.ProgramError.IncorrectProgramId)
      else if a.executable = true ∨ a.is_writable = false ∨ a.is_signer = true then
        ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)
      else ok (.Ok ())) := by
  unfold PoolL_canonical_header
  rw [PoolL_ProgramControl.control]
  by_cases ho : a.owner = id <;> cases he : a.executable <;>
    cases hw : a.is_writable <;> cases hs : a.is_signer <;>
    simp [ho,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
#print axioms control
end AspisR1.PoolL_CanonicalControl
end
