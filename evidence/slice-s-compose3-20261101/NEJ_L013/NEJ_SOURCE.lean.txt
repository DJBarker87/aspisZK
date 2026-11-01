import NEJ_ScannerFramed
set_option autoImplicit false
namespace NEJ_ScannerWidth
open Aeneas Aeneas.Std

/-- Digest::len is the length of a fixed eight-word carrier, not a callback.
The native step executes the actual len operation without stubbing it. -/
theorem width (digest : Array U32 8#usize) : digest.val.length = 8 := by
  exact digest.property

#print axioms width
end NEJ_ScannerWidth
