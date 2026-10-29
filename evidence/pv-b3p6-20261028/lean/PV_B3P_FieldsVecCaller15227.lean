import PV_B3P_FieldsVecState15227
import PV_B3P_FieldsCursor14227
namespace PV_B3P_Fields15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding13227 Result
set_option autoImplicit false

/-- The source caller's full Result retains the Vec on Rust Err, including
all successful earlier appends. The cursor carries the immutable input loan. -/
theorem fields_vec_cursor_projection15 (out : Bytes15) (values : List U32)
    (region : Nat) :
    (do let state ← fields_vec15 out values; .ok (erase_vec_state15 state)) =
      PV_B3P_Fields14227.cursor_fields14 append_bytes15 out.val
        (PV_B3P_Loans14227.cursor_new14 region values) := by
  rw [fields_vec_projection15]
  exact (PV_B3P_Fields14227.cursor_fields_binding14 append_bytes15 out.val region [] values).symm

/-- Honest explicit model witness uses the same append for every source step;
this does not assert infallible native allocation or instantiate the catalogue. -/
theorem fields_vec_joint_witness15 :
    PV_B3P_Link_fields append_bytes15 (PV_B3P_Fields14227.fields_source14 append_bytes15) :=
  PV_B3P_Fields14227.fields_source_link14 append_bytes15
#print axioms fields_vec_cursor_projection15
#print axioms fields_vec_joint_witness15
end PV_B3P_Fields15227
