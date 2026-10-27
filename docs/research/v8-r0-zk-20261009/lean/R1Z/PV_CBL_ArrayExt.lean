import R1Z.PV_CBL_ArrayPrefix
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ArrayExt
set_option autoImplicit false

theorem copied_unique {T : Type} [Inhabited T] {N : Usize} (a b : Array T N)
    (v : Slice T) (ha : PV_CBL_ArrayPrefix.copied a v N.val)
    (hb : PV_CBL_ArrayPrefix.copied b v N.val) : a=b := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp [a.property,b.property]
  · intro i hia hib
    have hn : i<N.val := by simpa [a.property] using hia
    have h := (ha i hn hn).trans (hb i hn hn).symm
    simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hia,
      List.getElem?_eq_getElem hib,Option.getD_some] using h

#print axioms copied_unique
end R1Z.PV_CBL_ArrayExt
