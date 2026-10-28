import NDO_JFv_PrefixRecord
set_option autoImplicit false
namespace AspisR1.JFv_RowOrder
open Aeneas Aeneas.Std Result

theorem get (row : U8) (bound : row.val<27) : ExtractedPrefixTrace.rowOrder[row.val]?=some row := by
  have values : ExtractedPrefixTrace.rowOrder.map UScalar.val=List.range 27 := rfl
  have h := congrArg (fun xs : List Nat => xs[row.val]?) values
  cases call : ExtractedPrefixTrace.rowOrder[row.val]? with
  | none => simp [List.getElem?_map,call,bound] at h
  | some actual =>
    have same : actual.val=row.val := by
      simpa only [List.getElem?_map,call,Option.map_some,List.getElem?_range bound,Option.some.injEq] using h
    exact congrArg some (UScalar.eq_of_val_eq same)

#print axioms get
end AspisR1.JFv_RowOrder
