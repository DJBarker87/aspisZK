import R1Z.PV_CBL_ArrayPrefix
import R1Z.PV_CBL_PadListFacts
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ArrayReadValue
set_option autoImplicit false
theorem read {T : Type} [Inhabited T] {N : Usize} (a : Array T N) (i : Usize)
    (h : i.val<N.val) : Array.index_usize a i = ok a.val[i.val]! := by
  have hi : i.val<a.val.length := by simpa only [a.property] using h
  simp only [Array.index_usize,Array.getElem?_Usize_eq,List.getElem?_eq_getElem hi,
    PV_CBL_PadListFacts.get_bang a.val i.val hi]
#print axioms read
end R1Z.PV_CBL_ArrayReadValue
