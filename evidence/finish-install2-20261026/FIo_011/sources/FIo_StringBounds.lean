import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisR1.FIo_StringBounds
example : "V1" = String.ofList ['V','1'] := rfl
example : "V1".toByteArray.size = 2 := by
  change (String.ofList ['V','1']).toByteArray.size=2
  rw [String.toByteArray_ofList]
  rfl
end AspisR1.FIo_StringBounds
