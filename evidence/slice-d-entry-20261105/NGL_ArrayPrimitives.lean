import NGJ_VERIFIER_IMPORT
set_option autoImplicit false
namespace NGL_ArrayPrimitives
open Aeneas Aeneas.Std Result
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount

theorem read {N : Usize} (a : Aeneas.Std.Array Account N) (i : Usize)
    (inside : i.val < a.val.length) (value : Account)
    (selected : a.val[i.val]? = some value) : Aeneas.Std.Array.index_usize a i = ok value := by
  cases a with
  | mk values sized =>
    simp_all [Aeneas.Std.Array.index_usize, instGetElem?ArrayUsizeLtNatValLengthValListEq]
#print axioms read
end NGL_ArrayPrimitives
