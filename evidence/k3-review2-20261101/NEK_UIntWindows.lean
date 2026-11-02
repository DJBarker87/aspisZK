import Init.Data.UInt.Lemmas
set_option autoImplicit false
namespace NEK_UIntWindows

/-- Assemble exactly the unsigned-byte division/remainder observations used by
K235--238. The correspondence with native Rust u8 is retained tool transport. -/
theorem byte_nibbles_ext (a b : UInt8)
    (high : a / 16 = b / 16) (low : a % 16 = b % 16) : a = b := by
  apply UInt8.toNat_inj.mp
  have h := congrArg UInt8.toNat high
  have l := congrArg UInt8.toNat low
  simp only [UInt8.toNat_div] at h
  simp only [UInt8.toNat_mod] at l
  change a.toNat / 16 = b.toNat / 16 at h
  change a.toNat % 16 = b.toNat % 16 at l
  calc
    a.toNat = a.toNat % 16 + 16 * (a.toNat / 16) := (Nat.mod_add_div _ _).symm
    _ = b.toNat % 16 + 16 * (b.toNat / 16) := by rw [h, l]
    _ = b.toNat := Nat.mod_add_div _ _

theorem indexed_bytes_ext {I : Type} (actual expected : I → UInt8)
    (high : ∀ i, actual i / 16 = expected i / 16)
    (low : ∀ i, actual i % 16 = expected i % 16) : actual = expected := by
  funext i
  exact byte_nibbles_ext (actual i) (expected i) (high i) (low i)

#print axioms byte_nibbles_ext
#print axioms indexed_bytes_ext
end NEK_UIntWindows
