import PV_B3P_FieldsModel13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false

def frontier_rows13 (append : AppendWord13) : List U8 → List (List U32) → Result FieldState13
  | out, [] => .ok (.Ok (),out)
  | out, row::rows => do
    let (status,out1) ← fields_model13 append out row
    match status with
    | .Err error => .ok (.Err error,out1)
    | .Ok () => frontier_rows13 append out1 rows

def PV_B3P_Link_frontier (append : AppendWord13)
    (source : List U8 → Array (Array U32 8#usize) 20#usize → Result FieldState13) : Prop :=
  ∀ out values, source out values =
    frontier_rows13 append out (values.val.map (fun row => row.val))

theorem frontier_stop13 (append : AppendWord13) (out written : List U8)
    (row : List U32) (rows : List (List U32))
    (error : aspis_core.state_only_prefix.r0.Error)
    (failed : fields_model13 append out row = .ok (.Err error,written)) :
    frontier_rows13 append out (row::rows) = .ok (.Err error,written) := by
  simp only [frontier_rows13,failed,bind_tc_ok]

theorem frontier_continue13 (append : AppendWord13) (out written : List U8)
    (row : List U32) (rows : List (List U32))
    (passed : fields_model13 append out row = .ok (.Ok (),written)) :
    frontier_rows13 append out (row::rows) = frontier_rows13 append written rows := by
  simp only [frontier_rows13,passed,bind_tc_ok]

theorem frontier_model_witness13 (append : AppendWord13) :
    ∃ source, PV_B3P_Link_frontier append source :=
  ⟨fun out values => frontier_rows13 append out (values.val.map (fun row => row.val)),fun _ _ => rfl⟩
#print axioms frontier_stop13
#print axioms frontier_continue13
#print axioms frontier_model_witness13
end PV_B3P_Binding13227
