import Init
set_option autoImplicit false
namespace PV_L2D_CtZero

def subtractP (x : UInt32) : UInt32 :=
  let mask := (0 : UInt32) - (if x ≥ 2147483647 then 1 else 0)
  x - ((2147483647 : UInt32) &&& mask)

def reduce64 (x : UInt64) : UInt32 :=
  let x : UInt64 := (x &&& (2147483647 : UInt64)) + (x >>> 31)
  let x : UInt64 := (x &&& (2147483647 : UInt64)) + (x >>> 31)
  subtractP x.toUInt32

/-- This is a single zero-input shape fact, not a full canonicality proof.
It is used only to preserve already-zero, excluded field coordinates. -/
theorem subtract_zero : subtractP 0=0 := by rfl
#print axioms subtract_zero

theorem reduce_zero : reduce64 0=0 := by rfl
#print axioms reduce_zero
end PV_L2D_CtZero
