import PV_EVH_FileDescWrite
set_option autoImplicit false
namespace PV_EVH_IOErrorOsBits

/-- Arithmetic normal form of the Linux64 bitpacked OS error variant. The
source cast/shift/or and pointer-provenance association are recorded separately;
these arithmetic facts alone are not a native io::Error representation proof. -/
def encode (code : Int) : Nat := (code % (2^32 : Int)).toNat * 2^32 + 2
def decode (bits : Nat) : Int :=
  let word : Nat := bits / 2^32
  if word < 2^31 then (word : Int) else (word : Int) - 2^32

theorem os_tag (code : Int) : encode code % 4 = 2 := by
  unfold encode
  omega

theorem nonnull (code : Int) : 0 < encode code := by
  unfold encode
  omega

theorem high_word (code : Int) :
    encode code / 2^32 = (code % (2^32 : Int)).toNat := by
  unfold encode
  omega

theorem roundtrip (code : Int) (lo : -(2^31 : Int) ≤ code)
    (hi : code < (2^31 : Int)) : decode (encode code) = code := by
  have hm : 0 ≤ code % (2^32 : Int) := Int.emod_nonneg _ (by positivity)
  have hb : code % (2^32 : Int) < (2^32 : Int) :=
    Int.emod_lt_of_pos _ (by positivity)
  unfold decode
  rw [high_word]
  dsimp only
  split <;> omega

/-- decode_repr's custom Box factory is selected ONLY by tag1. OS errors have
tag2, so their source destruction cannot enter that allocation's drop path.
This is control selection, never a claim of L3 silence or native TLS fidelity. -/
theorem not_custom (code : Int) : encode code % 4 ≠ 1 := by
  rw [os_tag]
  omega

#print axioms os_tag
#print axioms nonnull
#print axioms high_word
#print axioms roundtrip
#print axioms not_custom
end PV_EVH_IOErrorOsBits
