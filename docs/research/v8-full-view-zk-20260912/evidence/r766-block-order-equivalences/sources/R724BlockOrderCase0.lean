import AspisV8R19.R724BlockOrderMaps
/-! First bounded index-only round-trip cases for the pinned block maps. -/
set_option autoImplicit false
namespace AspisV8R19.R724BlockOrderCase0
open AspisV8R19.R724BlockOrderMaps

theorem rowOrder_inverse_at_zero : rowOrderInv (rowOrder 0) = 0 := by decide
#print axioms rowOrder_inverse_at_zero

theorem colOrder_inverse_at_zero : colOrderInv (colOrder 0) = 0 := by decide
#print axioms colOrder_inverse_at_zero
end AspisV8R19.R724BlockOrderCase0
