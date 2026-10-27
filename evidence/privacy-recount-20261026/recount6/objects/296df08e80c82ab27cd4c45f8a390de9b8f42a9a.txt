import R1Z.PV_CB_Field
import R1Z.ProverRwSuccessPointsSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_State
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_CB_Field.selected ops with
    op110 := ProverRwDictionaryEmbedding.embed
    op111 := .ok 18224775710398755665#u64
    op114 := ProverRwSuccessEquality.contextEq
    op118 := ProverRwSuccessPointsSource.state_only_prefix.r0.statement_points}
theorem op110_installed (ops : ExternalFuns) (x : aspis_core.field.M31) :
    (selected ops).op110 x = ProverRwDictionaryEmbedding.embed x := rfl
theorem op111_installed (ops : ExternalFuns) :
    (selected ops).op111 = .ok 18224775710398755665#u64 := rfl
theorem op114_installed (ops : ExternalFuns)
    (a b : aspis_core.state_only_hiding.StateOnlyHidingContext) :
    (selected ops).op114 a b = ProverRwSuccessEquality.contextEq a b := rfl
theorem op118_installed (ops : ExternalFuns) (x : Array aspis_core.field.QM31 10#usize) :
    (selected ops).op118 x =
      ProverRwSuccessPointsSource.state_only_prefix.state_only_statement_points x := rfl
#print axioms op110_installed
#print axioms op111_installed
#print axioms op114_installed
#print axioms op118_installed
end R1Z.PV_CB_State
