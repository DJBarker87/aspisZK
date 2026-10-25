import S6SliceFrameLengthV1
set_option autoImplicit false
namespace AspisS6SliceFrame

/-- Exact in-range write frame, retaining the original suffix after the write. -/
theorem setSlice_at_lead {T : Type} (lead suffix replacement : List T)
    (h : replacement.length ≤ suffix.length) :
    (lead++suffix).setSlice! lead.length replacement =
      lead++replacement++suffix.drop replacement.length := by
  simp [List.setSlice!,List.take_append,List.drop_append,
    List.take_of_length_le, h]

/-- Appending one checked chunk to an initialized output lead. -/
theorem setSlice_append_chunk {T : Type} (lead replacement : List T)
    (remaining : Nat) (zero : T) (h : replacement.length ≤ remaining) :
    (lead++List.replicate remaining zero).setSlice! lead.length replacement =
      (lead++replacement)++List.replicate (remaining-replacement.length) zero := by
  rw [setSlice_at_lead]
  · simp
  · simpa using h

#print axioms setSlice_at_lead
#print axioms setSlice_append_chunk
end AspisS6SliceFrame
