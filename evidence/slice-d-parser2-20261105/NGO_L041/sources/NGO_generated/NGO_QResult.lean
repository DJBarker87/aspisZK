import NGO_QAssociation
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_QResult
open NGO_QAssociation
noncomputable def specification (arr : Array U8 16#usize) : Option NGO_QRef.QM31 :=
  if word arr 0 >= 2147483647#u32 then none
  else if word arr 1 >= 2147483647#u32 then none
  else if word arr 2 >= 2147483647#u32 then none
  else if word arr 3 >= 2147483647#u32 then none
  else some ⟨⟨word arr 0,word arr 1⟩,⟨word arr 2,word arr 3⟩⟩
/-- Extracted native stub's exact complete Option, including every rejection. -/
theorem emitted (arr : Array U8 16#usize) :
    NGO_QRef.NGO_decode_le (Array.to_slice arr)=ok (specification arr) := by
  have w0 := (NGO_WordLaw.word arr 0#usize (by decide)).trans
    (congrArg ok (segment_word arr 0#usize 0 rfl (by decide)))
  have w1 := (NGO_WordLaw.word arr 4#usize (by decide)).trans
    (congrArg ok (segment_word arr 4#usize 1 rfl (by decide)))
  have w2 := (NGO_WordLaw.word arr 8#usize (by decide)).trans
    (congrArg ok (segment_word arr 8#usize 2 rfl (by decide)))
  have w3 := (NGO_WordLaw.word arr 12#usize (by decide)).trans
    (congrArg ok (segment_word arr 12#usize 3 rfl (by decide)))
  have length : Slice.len (Array.to_slice arr)=16#usize := by
    apply UScalar.eq_of_val_eq
    simpa using arr.property
  simp [NGO_QRef.NGO_decode_le,length,w0,w1,w2,w3,specification]
  split_ifs <;> rfl
#print axioms emitted
end NGO_QResult
