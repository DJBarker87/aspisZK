import PV_B3P_HelperRead224
import PV_B3P_HelperRow224
namespace PV_B3P_HelperEval224
open Aeneas Aeneas.Std PV_B3P_224
set_option autoImplicit false

def eval (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (chi : aspis_core.field.QM31) (r : Nat) :
    Result (core.result.Result aspis_core.field.QM31 reference224.Error) :=
  match rows.val[r]? with
  | none => .fail .arrayOutOfBounds
  | some row => reference224.one_row row chi

theorem at_index (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (chi : aspis_core.field.QM31) (r : Usize) (hr : r.val < 1024) :
    eval rows chi r.val = reference224.one_row (PV_B3P_HelperRead224.rowValue rows r hr) chi := by
  have hi : r.val < rows.val.length := by have h := rows.property; scalar_tac
  simp only [eval,List.getElem?_eq_getElem hi,PV_B3P_HelperRead224.rowValue]

theorem row_specification (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (chi : aspis_core.field.QM31) (r : Usize) (hr : r.val < 1024) :
    eval rows chi r.val = PV_B3P_HelperRow224.specification
      (PV_B3P_HelperRead224.rowValue rows r hr) chi := by
  rw [at_index rows chi r hr,PV_B3P_HelperRow224.complete_result]

#print axioms at_index
#print axioms row_specification
end PV_B3P_HelperEval224
