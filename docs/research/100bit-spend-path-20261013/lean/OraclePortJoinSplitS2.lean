import S2KaniHeaderReference

/-! Total extracted-reference header obligation. The linked Kani certificate
identifies the frozen parse_shape header cut under P6; it is not a Lean proof
of the rest of parse_shape, the observer-off caller or the independent tag. -/
set_option autoImplicit false
namespace AspisR1.OraclePortJoinSplitS2
open Aeneas Aeneas.Std Result

def headerModel (length : Usize) (magic : Bool) (tag : U8) (tail : Bool) : Bool :=
  if length = 57607#usize then
    if magic then if tag = 2#u8 then tail else false else false
  else false

theorem header_total (length : Usize) (magic : Bool) (tag : U8) (tail : Bool) :
    AspisS2HeaderRef.header_reference length magic tag tail =
      ok (headerModel length magic tag tail) := by
  unfold AspisS2HeaderRef.header_reference headerModel
  split
  · cases magic <;> simp only [Bool.false_eq_true, if_false, if_true]
    split <;> rfl
  · rfl

/-- A P6 source/reference equality suffices for total header replacement.
It remains an explicit proposition, never an added axiom. -/
theorem source_header_total
    (source : Usize → Bool → U8 → Bool → Result Bool)
    (P6_header : ∀ length magic tag tail,
      source length magic tag tail = AspisS2HeaderRef.header_reference length magic tag tail)
    (length : Usize) (magic : Bool) (tag : U8) (tail : Bool) :
    source length magic tag tail = ok (headerModel length magic tag tail) :=
  (P6_header length magic tag tail).trans (header_total length magic tag tail)

#print axioms header_total
#print axioms source_header_total
end AspisR1.OraclePortJoinSplitS2
