import R1Z.PDict_RejectionStd
import R1Z.PDict_PureSource
import R1Z.PDict_ConstantsSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_PureDictionary
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_RejectionStd.native
/-- Six complete core bodies and five constants-inclusive source bodies.
No external template or unknown callback implements these eleven fields. -/
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_RejectionStd.selected base ops with
    op37 := PDict_PureSource.aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq
    op40 := PDict_PureSource.aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone
    op41 := PDict_PureSource.aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq
    op43 := PDict_PureSource.aspis_core.field.wide_exact.WideExact.impl.c0
    op44 := PDict_PureSource.aspis_core.field.wide_exact.WideExact.impl.c1
    op60 := PDict_PureSource.aspis_core.field.CM31.new
    op235 := PDict_ConstantsSource.leaf_bits
    op236 := PDict_ConstantsSource.max_batch
    op239 := PDict_ConstantsSource.claims
    op240 := PDict_ConstantsSource.lanes
    op260 := PDict_ConstantsSource.domain
  }

theorem op37_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op37 = PDict_PureSource.aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq := rfl
#print axioms op37_installed

theorem op40_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op40 = PDict_PureSource.aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone := rfl
#print axioms op40_installed

theorem op41_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op41 = PDict_PureSource.aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq := rfl
#print axioms op41_installed

theorem op43_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op43 = PDict_PureSource.aspis_core.field.wide_exact.WideExact.impl.c0 := rfl
#print axioms op43_installed

theorem op44_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op44 = PDict_PureSource.aspis_core.field.wide_exact.WideExact.impl.c1 := rfl
#print axioms op44_installed

theorem op60_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op60 = PDict_PureSource.aspis_core.field.CM31.new := rfl
#print axioms op60_installed

theorem op235_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op235 = PDict_ConstantsSource.leaf_bits := rfl
#print axioms op235_installed

theorem op236_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op236 = PDict_ConstantsSource.max_batch := rfl
#print axioms op236_installed

theorem op239_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op239 = PDict_ConstantsSource.claims := rfl
#print axioms op239_installed

theorem op240_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op240 = PDict_ConstantsSource.lanes := rfl
#print axioms op240_installed

theorem op260_installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op260 = PDict_ConstantsSource.domain := rfl
#print axioms op260_installed
end R1Z.PDict_PureDictionary
