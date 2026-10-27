import XSg_RowTrace
import XRu_NewLength
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_NewRows
abbrev Q := aspis_core.field.QM31
abbrev Raw := XRu_NewStep.Raw
def row (q : Q) : XSg_RowPhase.Row :=
 Array.make 4#usize [UScalar.cast .U64 q.c0.a,UScalar.cast .U64 q.c0.b,
  UScalar.cast .U64 q.c1.a,UScalar.cast .U64 q.c1.b]
def Built (weights : Slice Q) (raw : Raw) (cursor : Nat) : Prop :=
 ∀ j, j<cursor → raw.val[j]?=(weights.val[j]?).map row
/-- Symbolic constructor-prefix installation. -/
theorem set (weights : Slice Q) (raw : Raw) (i : Usize) (q : Q)
 (built : Built weights raw i.val) (bound : i.val<raw.val.length)
 (get : weights.val[i.val]?=some q) : Built weights (raw.set i (row q)) (i.val+1) := by
 intro j hj
 change (raw.val.set i.val (row q))[j]?=(weights.val[j]?).map row
 by_cases same : j=i.val
 · subst j
   rw [List.getElem?_set_self bound,get]
   rfl
 · have old := built j (by omega)
   simpa only [List.getElem?_set,if_neg same,if_neg (Ne.symm same)] using old
/-- The finished constructor prefix determines every raw row, with no
concrete vector evaluation or canonicality assumption. -/
theorem final (weights : Slice Q) (raw : Raw) (len : raw.val.length=weights.val.length)
 (built : Built weights raw weights.val.length) : raw.val=weights.val.map row := by
 apply List.ext_getElem?
 intro j
 rw [List.getElem?_map]
 by_cases active : j<weights.val.length
 · exact built j active
 · rw [List.getElem?_eq_none_iff.mpr (by omega),List.getElem?_eq_none_iff.mpr (by omega)]
   rfl
#print axioms set
#print axioms final
end XSg_NewRows
