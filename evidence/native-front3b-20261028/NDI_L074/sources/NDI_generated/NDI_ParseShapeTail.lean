import NDI_PredicateLoops
import NDI_IteratorFrame
set_option autoImplicit false
namespace NDI_ParseShapeTail
open Aeneas Aeneas.Std Result

theorem zeros (xs : List U8) :
    List.anyM NDI_PredicatesRef.tail_predicate_ref xs=ok false ↔ ∀ x∈xs, x=0#u8 := by
  rw [NDI_PredicateLoops.tail]
  simp

theorem window (bytes : List U8) (fit : 16≤bytes.length) :
    ((bytes.drop 9).take 7).length=7 ∧
      (∀ j, j<7 → ((bytes.drop 9).take 7)[j]?=bytes[9+j]?) := by
  exact ⟨NDI_IteratorFrame.remainder bytes 9 7 (by omega),
    fun j h=>NDI_IteratorFrame.selected bytes 9 7 j h⟩

#print axioms zeros
#print axioms window
end NDI_ParseShapeTail
