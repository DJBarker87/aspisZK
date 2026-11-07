import NNG_EmittedContext
set_option autoImplicit false
namespace AspisR1.NNG_UsizeSmall
open Aeneas Aeneas.Std
/-- Portable small bound from the standard scalar carrier, without assuming
that the platform's opaque Usize size definition reduces to a numeral. -/
theorem size_gt_29 : 29 < UScalar.size .Usize := by
  rw [UScalar.size_UScalarTyUsize]
  have h := (29#usize).hmax
  have hs := Usize.size_scalarTac_eq.1
  scalar_tac
#print axioms size_gt_29
end AspisR1.NNG_UsizeSmall
