import PV_B3P_InternalMaps550227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

def internal_pair_source550 (state local1 : Array aspis_core.field.QM31 16#usize) :
    Result (Array aspis_core.field.QM31 16#usize) := do
  let weights ← rows_map550 (Array.index_usize local1)
  let evenConstants ← rows_map550 even_row550
  let oddConstants ← rows_map550 odd_row550
  let even ← reference_field.qm31_m31_dot weights evenConstants
  let odd ← reference_field.qm31_m31_dot weights oddConstants
  let next ← reference_poseidon.internal_round state even
  reference_poseidon.internal_round next odd

attribute [local irreducible] Array.index_usize reference_field.qm31_m31_dot
  reference_poseidon.internal_round Usize.wrapping_sub Usize.wrapping_mul Usize.wrapping_add

theorem internal_pair_reference550 (state local1 : Array aspis_core.field.QM31 16#usize) :
    internal_pair_source550 state local1 =
      reference_poseidon.interpolated_internal_pair state local1 := by
  unfold internal_pair_source550
  rw [weights_continuation550]
  simp only [even_continuation550,odd_continuation550]
  unfold reference_poseidon.interpolated_internal_pair
  rfl

theorem internal_pair_source_link550 :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_interpolated_internal_pair internal_pair_source550 :=
  funext fun state => funext (internal_pair_reference550 state)

#print axioms internal_pair_reference550
#print axioms internal_pair_source_link550
end PV_B3P_Association550227
