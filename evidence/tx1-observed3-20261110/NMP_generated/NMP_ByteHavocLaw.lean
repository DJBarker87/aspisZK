import NMP_CutAlgebra
set_option autoImplicit false
namespace AspisR1.NMP_ByteHavocLaw
open Aeneas Aeneas.Std
/-- Abstract postcondition of the auxiliary unit-returning frame contract.
Only one cell is tied to a recorded arbitrary choice; every other byte is free. -/
def Post (before after : List U8) (index : Nat) (word : U8) : Prop :=
 after.length=before.length ∧ after[index]?=some word
/-- Choosing the recorded word from ANY desired post-state admits that whole
post-state. Thus the generator restricts no returning mutable-byte value. -/
theorem covers (before after : List U8) (index : Nat)
 (size : after.length=before.length) (live : index<before.length) :
 ∃ word, Post before after index word := by
 have inside : index<after.length := by omega
 exact ⟨after[index],size,List.getElem?_eq_getElem inside⟩
/-- The chosen byte is exact, not a source-child functional law. -/
theorem chosen (before after : List U8) (index : Nat) (word : U8)
 (post : Post before after index word) : after[index]?=some word := post.2
#print axioms covers
#print axioms chosen
end AspisR1.NMP_ByteHavocLaw
