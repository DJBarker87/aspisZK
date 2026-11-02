import PV_B3P_PreparedNative14227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_PreparedNative14227
set_option autoImplicit false

theorem prepared_array_roundtrip550 (left : Array reference_field.PreparedQm31Multiplier 3#usize) :
    map_array14 to_reference14 (map_array14 from_reference14 left) = left := by
  apply Subtype.ext
  change (left.val.map from_reference14).map to_reference14 = left.val
  rw [List.map_map]
  have identity : to_reference14 ∘ from_reference14 = id := by
    funext value
    exact prepared_reverse_roundtrip14 value
  rw [identity, List.map_id]

/-- Nominal transport of the complete deployed nested-loop interpretation. -/
def prepared_source550 (left : Array reference_field.PreparedQm31Multiplier 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) : Result aspis_core.field.QM31 :=
  native_prepared14 (map_array14 from_reference14 left) right

theorem prepared_source_link550 :
    PV_B3P_Links13227.PV_B3P_Link_field_qm31_sum_products3_prepared prepared_source550 := by
  funext left right
  unfold prepared_source550
  rw [native_prepared_binding14, prepared_array_roundtrip550]

#print axioms prepared_array_roundtrip550
#print axioms prepared_source_link550
end PV_B3P_Association550227
