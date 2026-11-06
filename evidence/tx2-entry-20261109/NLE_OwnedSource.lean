import NLE_OwnedFold
import NIL_ResultCases
set_option autoImplicit false
noncomputable section
namespace NLE_Owned
open Aeneas Aeneas.Std Result AdapterRw
/-- Full nominal Result of the exact emitted caller, with every error/abort
prefix preserved by the log monad. This is a source fact, not native credit. -/
theorem source (ops : Ops) (initial : State) :
 (G ops initial).result = r1_pool_adapter.owned.stage2_owned ops
 initial.frame.program initial.frame.accounts initial.frame.data initial.frame.slot := by
 simp only [G,r1_pool_adapter.owned.stage2_owned,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_liftM,
  NJU_Log.erase_lift,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,errorMap_result]
 repeat' first
 | rfl
 | (apply NIL_ResultCases.bind_congr; intro value)
 | (fail_if_no_progress simp_all only [NJU_Log.erase_bind,NJU_Log.erase_record,
     NJU_Log.erase_liftM,NJU_Log.erase_lift,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,errorMap_result])
 | split
#print source
#print axioms source
end NLE_Owned
