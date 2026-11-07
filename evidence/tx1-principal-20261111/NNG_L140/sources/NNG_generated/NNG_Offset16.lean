import NNG_EmittedContext
set_option autoImplicit false
namespace AspisR1.NNG_Offset16
open Aeneas Aeneas.Std Result

def shifted (i : Usize) : Usize := Usize.wrapping_add 16#usize i

/-- A single symbolic scalar addition; the ten source indices cannot wrap. -/
theorem value (i : Usize) (hi : i.val < 10) : (shifted i).val = 16 + i.val := by
  unfold shifted
  scalar_tac
#print axioms value

theorem bound (i : Usize) (hi : i.val < 10) : (shifted i).val < 29 := by
  rw [value i hi]
  omega
#print axioms bound
end AspisR1.NNG_Offset16
