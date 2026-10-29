import PV_B3P_ClosureLinks14227
namespace PV_B3Q_ScalarEquality
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
/-- A shared scalar reference contributes its loaded bit-pattern value.
The source primitive comparisons have no stores, destructor or abort branch. -/
def source_eq {ty : UScalarTy} (left right : UScalar ty) : Result Bool :=
 .ok (decide (left.val=right.val))
def model_eq {ty : UScalarTy} (left right : UScalar ty) : Result Bool :=
 .ok (decide (left=right))
def source_ne {ty : UScalarTy} (left right : UScalar ty) : Result Bool :=
 .ok (decide (left.val≠right.val))
def model_ne {ty : UScalarTy} (left right : UScalar ty) : Result Bool :=
 .ok (decide (left≠right))
theorem eq_binding {ty : UScalarTy} (left right : UScalar ty) :
    source_eq left right = model_eq left right := by
 by_cases same : left=right
 · subst right; rfl
 · have different : left.val ≠ right.val := fun equal => same (UScalar.eq_of_val_eq equal)
   simp only [source_eq,model_eq,same,different,decide_false]
theorem ne_binding {ty : UScalarTy} (left right : UScalar ty) :
    source_ne left right = model_ne left right := by
 by_cases same : left=right
 · subst right; rfl
 · have different : left.val ≠ right.val := fun equal => same (UScalar.eq_of_val_eq equal)
   simp only [source_ne,model_ne,same,different,not_false_eq_true,decide_true]
inductive Body where | eq | ne
def Signature : (UScalarTy × Body) → Type := fun body =>
 UScalar body.1 → UScalar body.1 → Result Bool
def source : (body : UScalarTy × Body) → Signature body
 | (_, .eq) => source_eq
 | (_, .ne) => source_ne
def model : (body : UScalarTy × Body) → Signature body
 | (_, .eq) => model_eq
 | (_, .ne) => model_ne
theorem scalar_links : PV_B3P_Link_std_dependency_closure14 Signature source model := by
 intro body
 rcases body with ⟨ty,body⟩
 cases body with
 | eq => funext left right; exact eq_binding left right
 | ne => funext left right; exact ne_binding left right
#print axioms eq_binding
#print axioms ne_binding
#print axioms scalar_links
end PV_B3Q_ScalarEquality
