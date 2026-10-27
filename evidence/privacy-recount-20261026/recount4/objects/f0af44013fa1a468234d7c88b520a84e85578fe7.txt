import R1Z.ProverRwSuccessPointsSource
import R1Z.ProverRwSuccessCoefficientsSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessBodyInterpretation
open Aeneas Aeneas.Std Result ProverRwFull
-- The D coefficient path keeps the old callback. Only the common S1/S2
-- branch is installed from the retained extraction; no D table is supplied.
def coefficients [ExternalTypes] (ops : ExternalFuns) {T : Type} (copy : core.marker.Copy T)
    (v : transport.Variant) (rows : Array T 1024#usize) : Result (Array T 1024#usize) :=
  match v with
  | .D => ops.op255 copy v rows
  | .S1 | .S2 => ProverRwSuccessCoefficientsSource.transport.Variant.coefficients copy v rows
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessWideSource.selected ops with
    op118 := ProverRwSuccessPointsSource.state_only_prefix.r0.statement_points,
    op255 := coefficients ops}
theorem points_source (ops : ExternalFuns) (alpha : Array aspis_core.field.QM31 10#usize) :
    (selected ops).op118 alpha=
      ProverRwSuccessPointsSource.state_only_prefix.state_only_statement_points alpha := rfl

theorem coefficients_s2 (ops : ExternalFuns) {T : Type} (copy : core.marker.Copy T)
    (rows : Array T 1024#usize) :
    (selected ops).op255 copy .S2 rows=
      ProverRwSuccessCoefficientsSource.transport.Variant.coefficients copy .S2 rows := rfl

theorem coefficients_d (ops : ExternalFuns) {T : Type} (copy : core.marker.Copy T)
    (rows : Array T 1024#usize) :
    (selected ops).op255 copy .D rows=ops.op255 copy .D rows := rfl
#print axioms points_source
#print axioms coefficients_s2
#print axioms coefficients_d
end R1Z.ProverRwSuccessBodyInterpretation
