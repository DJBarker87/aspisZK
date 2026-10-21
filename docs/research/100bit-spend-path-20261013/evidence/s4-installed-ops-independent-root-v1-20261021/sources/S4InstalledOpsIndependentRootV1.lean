import S4FourCallbacksForwardRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsInstalledOpsIndependentRootV1
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
open AspisR1FastDotsFourCallbacksForwardRootV1 (install)
/-- Every field of the selected operation record is fixed by installation.
The apparent free base supplies no operation to the model execution. This
identifies a concrete model; source/runtime correspondence is still separate. -/
theorem installed_ops_independent (a b : Ops) : install a = install b := rfl

/-- Therefore the complete source-shaped original model call is independent
of the apparent base record, including all failure branches. -/
theorem four_dots_base_independent (a b : Ops) (q : Slice U8)
    (g : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize) :
    AspisR1FastDotsCurrent.fast_dots.four_dots (install a) q g =
      AspisR1FastDotsCurrent.fast_dots.four_dots (install b) q g := by
  rw [installed_ops_independent a b]
#print axioms installed_ops_independent
#print axioms four_dots_base_independent
end AspisR1FastDotsInstalledOpsIndependentRootV1
