import PCD_LaneRef.Types
set_option autoImplicit false
namespace PCD_ArrayExt
open Aeneas.Std

theorem scalar_ext {ty : UScalarTy} (x y : UScalar ty) (same : x.val = y.val) : x = y := by
  cases x with
  | mk xb =>
    cases y with
    | mk yb =>
      have eq : xb = yb := BitVec.eq_of_toNat_eq same
      cases eq
      rfl

theorem array_ext {ty : UScalarTy} {n : Usize}
    (x y : Array (UScalar ty) n)
    (same : ∀ i : Fin n.val,
      (x.val[i.val]'(by rw [x.property]; exact i.isLt)).val =
      (y.val[i.val]'(by rw [y.property]; exact i.isLt)).val) : x = y := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact x.property.trans y.property.symm
  · intro i hx hy
    apply scalar_ext
    exact same ⟨i, by rw [← x.property]; exact hx⟩
#print axioms scalar_ext
#print axioms array_ext
end PCD_ArrayExt
