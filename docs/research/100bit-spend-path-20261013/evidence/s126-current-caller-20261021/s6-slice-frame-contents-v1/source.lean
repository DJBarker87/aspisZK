import S6SliceFrameLengthV1
set_option autoImplicit false
namespace AspisS6SliceFrame

/-- Exact in-range write frame, retaining the original suffix after the write. -/
theorem setSlice_at_prefix {T : Type} (prefix suffix replacement : List T)
    (h : replacement.length ≤ suffix.length) :
    (prefix++suffix).setSlice! prefix.length replacement =
      prefix++replacement++suffix.drop replacement.length := by
  simp [List.setSlice!,List.take_append,List.drop_append,
    List.take_of_length_le, h]

/-- Appending one checked chunk to an initialized output prefix. -/
theorem setSlice_append_chunk {T : Type} (prefix replacement : List T)
    (remaining : Nat) (zero : T) (h : replacement.length ≤ remaining) :
    (prefix++List.replicate remaining zero).setSlice! prefix.length replacement =
      (prefix++replacement)++List.replicate (remaining-replacement.length) zero := by
  rw [setSlice_at_prefix]
  · simp
  · simpa using h

#print axioms setSlice_at_prefix
#print axioms setSlice_append_chunk
end AspisS6SliceFrame
