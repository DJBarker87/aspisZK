import NBJ_Padding

set_option autoImplicit false
namespace AspisR1.NBJ_PaddingBits
open Aeneas Aeneas.Std Result

/-- Both directions of the byte predicate, connecting the native eight-byte
nonzero observation to the installed little-endian word without an assumed
padding result. Only the fixed8-byte zero value is reduced. -/
theorem zero_iff (word : Array U8 8#usize) :
    core.num.U64.from_le_bytes word = 0#u64 ↔ ∀ b ∈ word.val, b = 0#u8 := by
  constructor
  · exact Port4B_ByteWord.u64_zero word
  · intro zero
    have same : word = Array.repeat 8#usize 0#u8 := by
      apply Subtype.ext
      change word.val = List.replicate 8 0#u8
      apply List.eq_replicate_iff.mpr
      exact ⟨word.property,zero⟩
    rw [same]
    rfl

#print axioms zero_iff
end AspisR1.NBJ_PaddingBits
