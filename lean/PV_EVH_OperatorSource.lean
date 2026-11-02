import PV_EVH_ResultOps
import PV_EVH_VariantGuard
import R1Z.ProverRwSuccessOptions
import R1Z.ProverRwOuterMapErr
import R1Z.ProverRwCallerBinding
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OperatorSource
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
/-- Reuse actual recorded source bindings, not a fresh model dictionary.
Native event/drop and opsNative-preservation obligations are still separate. -/
theorem map_source {T E U F : Type} (inst : core.ops.function.FnOnce F T U)
    (r : core.result.Result T E) (closure : F) :
    R1Z.ProverRwSuccessOptions.resultMap inst r closure =
      PV_EVH_ResultOps.sourceMap inst r closure := by
  cases r <;> rfl

theorem mapErr_source {T E F O : Type} (inst : core.ops.function.FnOnce O E F)
    (r : core.result.Result T E) (closure : O) :
    R1Z.ProverRwOuterMapErr.map_err inst r closure =
      PV_EVH_ResultOps.sourceMapErr inst r closure := by
  cases r <;> rfl

theorem variant_source (a b : transport.Variant) :
    R1Z.ProverRwCallerBinding.variantEq a b = PV_EVH_VariantGuard.equal a b := by
  cases a <;> cases b <;> rfl

theorem selected_map (ops : ExternalFuns) {T E U F : Type}
    (inst : core.ops.function.FnOnce F T U) (r : core.result.Result T E) (closure : F) :
    (R1Z.ProverRwSuccessOptions.selected ops).op11 inst r closure =
      PV_EVH_ResultOps.sourceMap inst r closure := map_source inst r closure

theorem selected_mapErr (ops : ExternalFuns) {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (r : core.result.Result T E) (closure : O) :
    (R1Z.ProverRwOuterMapErr.selected ops).op12 inst r closure =
      PV_EVH_ResultOps.sourceMapErr inst r closure := mapErr_source inst r closure

theorem selected_variant (ops : ExternalFuns) (a b : transport.Variant) :
    (R1Z.ProverRwCallerBinding.install ops).op233 a b =
      PV_EVH_VariantGuard.equal a b := variant_source a b
#print axioms map_source
#print axioms mapErr_source
#print axioms variant_source
#print axioms selected_map
#print axioms selected_mapErr
#print axioms selected_variant
end PV_EVH_OperatorSource
