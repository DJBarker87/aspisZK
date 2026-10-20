import AspisR1QueryGeometryActual.Funs
open Aeneas Aeneas.Std
set_option autoImplicit false
namespace R17ArrayIndexMake

theorem index_make_get {α : Type} (n : Usize) (xs : List α)
    (hn : xs.length = n.val) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize (Array.make n xs hn) i = .ok xs[i.val] := by
  simp [Array.index_usize, Array.make, hn, hi]

#print axioms index_make_get
end R17ArrayIndexMake
