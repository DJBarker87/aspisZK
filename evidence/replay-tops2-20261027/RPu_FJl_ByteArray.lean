import R1M31ParserArray
import MultiproofConeCanonical
set_option autoImplicit false
namespace AspisR1.FJl_ByteArray
open Aeneas Aeneas.Std
/-- Arbitrary four-byte input has exactly the retained byte-function shape. -/
theorem source (a : Array U8 4#usize) :
    M31ParserRefinement.wordArray (M31ParserArray.arrayBytes a)=a := by
  exact M31ParserArray.wordArray_arrayBytes a

theorem list (a : Array U8 4#usize) :
    List.ofFn (M31ParserArray.arrayBytes a)=MultiproofConeCanonical.bytesOf a.val := by
  have len : a.val.length=4 := a.property
  apply List.ext_getElem
  · simp only [List.length_ofFn,MultiproofConeCanonical.bytesOf,List.length_map,len]
  · intro i hi hj
    simp only [List.getElem_ofFn,MultiproofConeCanonical.bytesOf,List.getElem_map,
      M31ParserArray.arrayBytes]

#print axioms source
#print axioms list
end AspisR1.FJl_ByteArray
