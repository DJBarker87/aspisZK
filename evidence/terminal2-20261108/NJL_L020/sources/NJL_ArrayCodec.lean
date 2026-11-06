import NJB_ArrayCarrier
import NJB_DecodeInjective
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_ArrayCodec
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
/-- Lift complete canonical pointwise equality to the SAME full raw array,
using the predecessor's proved field injectivity. No native address premise. -/
theorem ext {N : Usize} (a b : Array NQ N)
 (ha : FIw_ArrayValue.canonical a) (hb : FIw_ArrayValue.canonical b)
 (same : FIw_ArrayValue.decoded a=FIw_ArrayValue.decoded b) : a=b := by
 apply NJB_DecodeInjective.array a b ha hb
 apply List.ext_getElem
 · simp only [List.length_map,a.property,b.property]
 · intro i hi hj
   have bound : i<N.val := by simpa only [List.length_map,a.property] using hi
   exact congrFun same ⟨i,bound⟩
#print axioms ext
end AspisR1.NJL_ArrayCodec
end
