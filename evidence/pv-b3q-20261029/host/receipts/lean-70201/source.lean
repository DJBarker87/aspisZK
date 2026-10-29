import PV_B3Q_MatrixStore
namespace PV_B3Q_Matrix
open Aeneas Aeneas.Std PV_B3P_Binding14227
set_option autoImplicit false
/-- Three rows of three raw stored words, before field reconstruction. -/
def entries (sums : Matrix14) : List (List U64) := sums.val.map (fun row => row.val)
theorem entries_injective (a b : Matrix14) (same : entries a = entries b) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact a.property.trans b.property.symm
  · intro i ha hb
    apply Subtype.ext
    have h := congrArg (fun xs : List (List U64) => xs[i]?) same
    simp only [entries, List.getElem?_map, List.getElem?_eq_getElem ha,
      List.getElem?_eq_getElem hb, Option.map_some] at h
    exact Option.some.inj h
#print axioms entries_injective
end PV_B3Q_Matrix
