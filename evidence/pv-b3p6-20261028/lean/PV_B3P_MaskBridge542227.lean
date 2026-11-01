import PV_B3P_MaskSource542227
namespace PV_B3P_MaskSource542227
open Aeneas Aeneas.Std PV_B3P_Direct17227 PV_B3P_Correct14227
set_option autoImplicit false

/-- Deployed extracted mask body with the two ordinary wrappers bound
statement by statement. Intrinsic implementation remains V370/D381/D386. -/
def mask_source542 (values : Array PV_B3P_227.aspis_core.field.QM31 16#usize)
    (mask : U16) :=
  host_copy_terminal.selector_mask_sum_16 count_ones_source542 trailing_zeros_source542 values mask

theorem mask_source_reference542
    (values : Array PV_B3P_227.aspis_core.field.QM31 16#usize) (mask : U16)
    (allowed : MaskAllowed mask) :
    mask_source542 values mask =
      PV_B3P_227.reference_copy_terminal.selector_mask_sum_16 values mask :=
  mask_extraction_reference_on_domain17 count_ones_source542 trailing_zeros_source542
    mask_integer_source_laws542 values mask allowed

theorem mask_source_continuation542 {β : Type}
    (values : Array PV_B3P_227.aspis_core.field.QM31 16#usize) (mask : U16)
    (allowed : MaskAllowed mask)
    (next : PV_B3P_227.aspis_core.field.QM31 → Result β) :
    (do let sum ← mask_source542 values mask; next sum) =
    (do let sum ← PV_B3P_227.reference_copy_terminal.selector_mask_sum_16 values mask;
        next sum) := by
  rw [mask_source_reference542 values mask allowed]

/-- No declaration of intrinsic semantics is installed as an axiom. This
explicit interface states precisely what V370 must preserve for an external
implementation. It is a local compiler-boundary statement, never a T field. -/
theorem mask_external_boundary542 (ones zeros : U16 → Result U32)
    (count_boundary : ones = count_ones_source542)
    (trail_boundary : zeros = trailing_zeros_source542)
    (values : Array PV_B3P_227.aspis_core.field.QM31 16#usize) (mask : U16)
    (allowed : MaskAllowed mask) :
    host_copy_terminal.selector_mask_sum_16 ones zeros values mask =
      PV_B3P_227.reference_copy_terminal.selector_mask_sum_16 values mask := by
  subst ones
  subst zeros
  exact mask_source_reference542 values mask allowed

#print axioms mask_source_reference542
#print axioms mask_source_continuation542
#print axioms mask_external_boundary542
end PV_B3P_MaskSource542227
