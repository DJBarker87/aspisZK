import NLE_WrapperFold
import NIL_ResultCases
set_option autoImplicit false
noncomputable section
namespace NLE_Wrapper
open Aeneas Aeneas.Std Result
/-- Parameterized local wrapper fold. Only source transcription is established;
SDK/native call-site packets are not inferred from this equality. -/
theorem fold_source {Account : Type} (ops : Ops Account) (state : State Account) :
 (G ops state).result = source ops state := by
 simp only [G,source,snapshot,clear,NJU_Log.erase_bind,NJU_Log.erase_record,
  NJU_Log.erase_liftM,NJU_Log.erase_lift,NJU_Log.erase_pure,NJU_Log.erase_if,
  NJU_Log.prod_cases,bind_tc_ok,bind_assoc_eq]
 repeat' first
 | rfl
 | (apply NIL_ResultCases.bind_congr; intro value)
 | (fail_if_no_progress simp_all only [NJU_Log.erase_bind,NJU_Log.erase_record,
     NJU_Log.erase_liftM,NJU_Log.erase_lift,NJU_Log.erase_pure,NJU_Log.erase_if,
     NJU_Log.prod_cases,bind_tc_ok,bind_assoc_eq])
 | split
#print fold_source
#print axioms fold_source
end NLE_Wrapper
