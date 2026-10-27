import RPt_BEm_PaddingModel
set_option autoImplicit false
namespace AspisR1.BEm_ByteWord
open Aeneas.Std BEm_PaddingModel

/-- Native byte carrier for the isolated8-byte source padding cut. -/
structure Bytes where
  b0 : U8
  b1 : U8
  b2 : U8
  b3 : U8
  b4 : U8
  b5 : U8
  b6 : U8
  b7 : U8

def word (b : Bytes) : Word := ⟨b.b0.val,b.b1.val,b.b2.val,b.b3.val,
  b.b4.val,b.b5.val,b.b6.val,b.b7.val⟩

theorem admitted (b : Bytes) : valid (word b) := by
  intro x member
  simp only [bytes,word,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> scalar_tac

/-- No free byte-bound premise; all eight native bytes are quantified. This
is arithmetic agreement, not a source/extraction or physical-loop certificate. -/
theorem agreement (b : Bytes) : nativeWord (word b) = referenceWord (word b) :=
  BEm_PaddingModel.word _ (admitted b)

#print axioms admitted
#print axioms agreement
end AspisR1.BEm_ByteWord
