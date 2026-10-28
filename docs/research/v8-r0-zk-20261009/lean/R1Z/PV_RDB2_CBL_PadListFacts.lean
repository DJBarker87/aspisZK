import R1Z.PV_RDB2_CBL_PaddingModel
import R1Z.PV_RDB2_CBL_ArrayPrefix
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadListFacts
set_option autoImplicit false
theorem get_bang {T : Type} [Inhabited T] (l : List T) (i : Nat) (h : i<l.length) :
    l[i]! = l[i] := by
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
theorem ext {T : Type} [Inhabited T] (a b : List T) (hlen : a.length=b.length)
    (h : ∀ i, i<a.length → a[i]! = b[i]!) : a=b := by
  apply List.ext_getElem hlen
  intro i hi hj
  simpa only [get_bang a i hi,get_bang b i hj] using h i hi
#print axioms get_bang
#print axioms ext
end R1Z.PV_CBL_PadListFacts
