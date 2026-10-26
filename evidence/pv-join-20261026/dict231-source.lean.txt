import R1Z.PDict_CodecDictionary
import R1Z.PDict_RemainingLeafSource
import R1Z.ProverRwP7FibreSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingDictionary231
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_CodecDictionary.native
/-- Actual extracted ct-host-prover bodies, extending the same simultaneous
selector. The tracing-feature implementation is not selected by this cut. -/
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_CodecDictionary.selected base ops with
    op78 := @ProverRwP7FibreSource.fibre
    op231 := PDict_RemainingLeafSource.aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
    op247 := PDict_RemainingLeafSource.aspis_r1_cost_probe.trace.value }

theorem op78_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {E : Type}
    (field : aspis_core.r0.scalar.CodeField E) (i : aspis_core.r0.domain.FibreIndex) :
    (selected base ops).op78 field i = ProverRwP7FibreSource.fibre field i := rfl

theorem op231_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op231 =
    PDict_RemainingLeafSource.aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone := rfl

theorem op247_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op247 =
    PDict_RemainingLeafSource.aspis_r1_cost_probe.trace.value := rfl

#print axioms op78_installed
#print axioms ProverRwP7FibreSource.fibre
#print axioms op231_installed
#print axioms op247_installed
end R1Z.PDict_RemainingDictionary231
