import AspisR1BatchedFoldArithmetic
import ExtractedCurrentReducer

set_option autoImplicit false

namespace AspisR1BatchedReducerBridge

open Aeneas.Std

private def u64OfNat (n : Nat) (hn : n < 2 ^ 64) : U64 :=
  UScalar.ofNatCore n hn

/-- Finishing a source-shaped batch stream through the retained actual
`M31.reduce_u64` has the same canonical value as the unreduced product sum. -/
theorem actual_finish_mod (n total : Nat) (hn : n < 2 ^ 64)
    (hres : n % AspisR1BatchedFoldArithmetic.modulus =
      total % AspisR1BatchedFoldArithmetic.modulus) :
    ∃ z : AspisR1Qm31ArithmeticProbe.field.M31,
      AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64
        (u64OfNat n hn) = .ok z ∧
      z.val = total % AspisR1BatchedFoldArithmetic.modulus ∧
      z.val < AspisR1BatchedFoldArithmetic.modulus := by
  obtain ⟨z, hz, hmod, hcanonical⟩ :=
    AspisR1.ExtractedCurrentReducer.current_wrapper_mod (u64OfNat n hn)
  have hvalue : (u64OfNat n hn).val = n := rfl
  rw [hvalue] at hmod
  refine ⟨z, hz, hmod.trans hres, ?_⟩
  simpa [AspisR1BatchedFoldArithmetic.modulus] using hcanonical

#print axioms actual_finish_mod

end AspisR1BatchedReducerBridge
