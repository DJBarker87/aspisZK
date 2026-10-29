import PV_DIAG4_ReprDrop
import Lean.Elab.Tactic.Omega
/-! Bit-pattern arithmetic needed by the OS Error Repr association. This
proves the word arithmetic, not native pointer provenance or arbitrary enum
validity. No changed extraction or foreign-call law is introduced. -/
set_option autoImplicit false
namespace PV_DIAG4
def signed32 (code : Fin (2^32)) : Int :=
 if code.val < 2^31 then (code.val : Int) else (code.val : Int) - 2^32
theorem os_word_nonzero (code : Fin (2^32)) : 0 < osWord code := by
 unfold osWord; omega
#print axioms os_word_nonzero
theorem os_word_bound (code : Fin (2^32)) : osWord code < 2^64 := by
 have hc := code.isLt
 unfold osWord; omega
#print axioms os_word_bound
theorem os_word_high (code : Fin (2^32)) : osWord code / 2^32 = code.val := by
 unfold osWord; omega
#print axioms os_word_high
theorem signed32_range (code : Fin (2^32)) :
 -(2^31 : Int) ≤ signed32 code ∧ signed32 code < 2^31 := by
 have hc := code.isLt
 unfold signed32; split <;> omega
#print axioms signed32_range
theorem signed32_pattern (code : Fin (2^32)) :
 signed32 code % 2^32 = (code.val : Int) := by
 have hc := code.isLt
 unfold signed32; split <;> omega
#print axioms signed32_pattern
theorem stored_eintr_exact (code : Fin (2^32)) :
 signed32 code = 4 ↔ code.val = 4 := by
 have hc := code.isLt
 unfold signed32; split <;> omega
#print axioms stored_eintr_exact
end PV_DIAG4
