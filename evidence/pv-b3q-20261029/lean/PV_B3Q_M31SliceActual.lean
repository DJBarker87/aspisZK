import PV_B3P_E227_01
import PV_B3Q_SliceActual
namespace PV_B3Q_M31SliceActual
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
def source (left right : Slice U32) : Result Bool :=
 PV_B3Q_SliceEqual.source PV_B3Q_SliceEqualityValue.scalar_ne left.val right.val
def model (left right : Slice U32) : Result Bool :=
 Aeneas.Std.core.slice.cmp.PartialEqSlice.eq PV_B3P_227.aspis_core.field.M31.Insts.CoreCmpPartialEqM31 left right
/-- The pinned library's total-correctness specification fixes the actual
comparison result, rather than substituting a fresh model definition. -/
theorem model_value (left right : Slice U32) : model left right = .ok (decide (left=right)) := by
 have specification := Aeneas.Std.core.slice.cmp.PartialEqSlice.eq_homo_spec
   PV_B3P_227.aspis_core.field.M31.Insts.CoreCmpPartialEqM31 left right (by
     intro x y
     change (!decide (x=y) = true ↔ x≠y)
     simp)
 change WP.spec (model left right) _ at specification
 cases evaluated : model left right with
 | fail error =>
   rw [evaluated] at specification
   exact False.elim specification
 | div =>
   rw [evaluated] at specification
   exact False.elim specification
 | ok value =>
   rw [evaluated] at specification
   change (value=true ↔ left=right) at specification
   have same : value = decide (left=right) := by
     cases value <;> simp_all
   exact congrArg Result.ok same

theorem source_binding (left right : Slice U32) : source left right = model left right := by
 unfold source
 rw [PV_B3Q_SliceEqualityValue.source_value,model_value]
 by_cases same : left=right
 · subst right
   simp
 · have different : left.val≠right.val := fun equal => same (Subtype.ext equal)
   simp only [same,different,decide_false]

theorem actual_slice_link : PV_B3P_Link_std_dependency_closure14
    (fun _ : Unit => Slice U32 → Slice U32 → Result Bool)
    (fun _ => source) (fun _ => model) := by
 intro _
 funext left right
 exact source_binding left right
#print axioms model_value
#print axioms source_binding
#print axioms actual_slice_link
end PV_B3Q_M31SliceActual
