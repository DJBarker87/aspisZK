import NNX_Gather
set_option autoImplicit false
namespace AspisR1.NNX_ArrayRead
open Aeneas Aeneas.Std Result
/-- Generic source read: the bound is on the underlying list, avoiding
normalization of specialized nominal array lengths during simplification. -/
theorem source {T : Type} {n : Usize} (a : Array T n) (i : Usize)
 (inside : i.val<a.val.length) :
 Array.index_usize a i = .ok (a.val[i.val]'inside) := by
 simp only [Array.index_usize,Array.getElem?_Usize_eq,List.getElem?_eq_getElem inside]
#print axioms source
end AspisR1.NNX_ArrayRead
