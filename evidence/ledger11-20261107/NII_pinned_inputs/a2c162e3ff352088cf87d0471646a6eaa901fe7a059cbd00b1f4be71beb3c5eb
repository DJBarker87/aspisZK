import NGL_ArrayPrimitives
import NGL_ReadonlyModel
import NFQ_ZeroPrimitives
set_option autoImplicit false
noncomputable section
namespace NGL_DistinctStep
open Aeneas Aeneas.Std Result ControlFlow
attribute [local instance] Classical.propDecidable
abbrev Account := NGL_ArrayPrimitives.Account
abbrev PE := AdapterRw.solana_program_error.ProgramError

theorem step {N : Usize} (ops : AdapterRw.Ops) (a : Array Account N)
    (index previous : Usize) (inIndex : index.val < a.val.length)
    (inPrevious : previous.val < index.val) :
    AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body
      (NGL_ReadonlyModel.install ops) a index previous =
      (if (a.val[previous.val]'(by omega)).key = a.val[index.val].key then
        ok (done (some (core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidArgument)))
       else ok (cont (Usize.wrapping_add previous 1#usize))) := by
  have within : previous.val < a.val.length := by omega
  have left := NGL_ArrayPrimitives.read a previous within a.val[previous.val]
    (List.getElem?_eq_getElem within)
  have right := NGL_ArrayPrimitives.read a index inIndex a.val[index.val]
    (List.getElem?_eq_getElem inIndex)
  simp only [AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body,
    if_pos (show previous < index from inPrevious),left,right,
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.key,bind_tc_ok,NGL_ReadonlyModel.install]
  by_cases same : a.val[previous.val].key = a.val[index.val].key <;> simp [same,lift]

theorem exit {N : Usize} (ops : AdapterRw.Ops) (a : Array Account N)
    (index previous : Usize) (outside : ¬ previous < index) :
    AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body ops a index previous =
      ok (done none) := by
  simp only [AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body,
    if_neg outside]
#print axioms exit
#print axioms step
end NGL_DistinctStep
