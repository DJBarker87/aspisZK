import LPf_BaseMultiply
set_option autoImplicit false
namespace AspisR1.LPf_ArithmeticWitnesses
open Aeneas Aeneas.Std Result

/-- Local source-domain non-vacuity; no actual-top joint witness is asserted. -/
theorem zero : ∃ z,
    FIo_Native.fast_pairing.canonical.reduce 0#u64 = ok z ∧ z.val = 0 := by
  obtain ⟨z, run, value, _⟩ := LPf_ReductionWord.native_reduce 0#u64
  exact ⟨z,run,by simpa using value⟩

theorem full_word : ∃ z,
    FIo_Native.fast_pairing.canonical.reduce 18446744073709551615#u64 = ok z ∧ z.val = 3 := by
  obtain ⟨z, run, value, _⟩ := LPf_ReductionWord.native_reduce 18446744073709551615#u64
  refine ⟨z,run,?_⟩
  change z.val = (18446744073709551615 : Nat) % 2147483647 at value
  norm_num only [Nat.reduceMod] at value
  exact value

theorem nonzero_product : ∃ z,
    FIo_Native.aspis_core.field.M31.mul 1#u32 1#u32 = ok z ∧ z.val = 1 := by
  obtain ⟨z, run, value, _⟩ := LPf_BaseMultiply.source 1#u32 1#u32
  exact ⟨z,run,by simpa using value⟩

#print axioms zero
#print axioms full_word
#print axioms nonzero_product
end AspisR1.LPf_ArithmeticWitnesses
