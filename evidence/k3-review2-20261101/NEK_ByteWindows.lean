/-! Exact assembly for split native byte observations. No source refinement is
assumed or claimed here; the caller supplies both native window facts. -/
set_option autoImplicit false
namespace NEK_ByteWindows

theorem quotient_remainder_ext (a b radix : Nat)
    (quotient : a / radix = b / radix)
    (remainder : a % radix = b % radix) : a = b := by
  calc
    a = a % radix + radix * (a / radix) := (Nat.mod_add_div a radix).symm
    _ = b % radix + radix * (b / radix) := by rw [quotient, remainder]
    _ = b := Nat.mod_add_div b radix

theorem indexed_nibbles_ext {I : Type} (actual expected : I → Nat)
    (high : ∀ i, actual i / 16 = expected i / 16)
    (low : ∀ i, actual i % 16 = expected i % 16) : actual = expected := by
  funext i
  exact quotient_remainder_ext (actual i) (expected i) 16 (high i) (low i)

#print axioms quotient_remainder_ext
#print axioms indexed_nibbles_ext
end NEK_ByteWindows
