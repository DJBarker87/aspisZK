import NMX_ErrorCloneCut
set_option autoImplicit false
noncomputable section
namespace NMX_LengthCloneCut
open Aeneas Aeneas.Std Result AdapterRw
/-- The actual Result::clone occurrence preserves a scalar value and reaches
ProgramError::clone only on the deferred-error arm. -/
theorem shape (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount) :
 r1_pool_adapter.owned.OwnedAccount.data_len ops a =
 match a.length with
 | .Ok n => ok (.Ok n)
 | .Err e => (do let cloned ← ops.op35 e; ok (.Err cloned)) := by
 cases h : a.length <;>
  simp only [r1_pool_adapter.owned.OwnedAccount.data_len,
   core.result.Result.Insts.CoreCloneClone.clone,h,
   solana_program_error.ProgramError.Insts.CoreCloneClone,
   core.clone.CloneUsize,bind_tc_ok]
#print axioms shape
end NMX_LengthCloneCut
end
