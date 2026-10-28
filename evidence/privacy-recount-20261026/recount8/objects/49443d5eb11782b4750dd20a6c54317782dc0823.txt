import R1Z.PDict_FileCarrier
import R1Z.PDict_RejectionStdSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RejectionStd
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_FileCarrier.native
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_FileCarrier.selected base ops with
    op5 := PDict_RejectionStdSource.core.option.Option.is_some_and
    op6 := PDict_RejectionStdSource.core.option.Option.as_ref
    op7 := PDict_RejectionStdSource.core.option.Option.ok_or
    op8 := PDict_RejectionStdSource.core.option.Option.Insts.CoreCmpPartialEqOption.eq
    op9 := PDict_RejectionStdSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch
    op10 := PDict_RejectionStdSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    op11 := PDict_RejectionStdSource.core.result.Result.map
  }

theorem op5_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op5 (native base) (selected base ops) =
      @PDict_RejectionStdSource.core.option.Option.is_some_and := rfl

theorem op6_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op6 (native base) (selected base ops) =
      @PDict_RejectionStdSource.core.option.Option.as_ref := rfl

theorem op7_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op7 (native base) (selected base ops) =
      @PDict_RejectionStdSource.core.option.Option.ok_or := rfl

theorem op8_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op8 (native base) (selected base ops) =
      @PDict_RejectionStdSource.core.option.Option.Insts.CoreCmpPartialEqOption.eq := rfl

theorem op9_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op9 (native base) (selected base ops) =
      @PDict_RejectionStdSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch := rfl

theorem op10_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op10 (native base) (selected base ops) =
      @PDict_RejectionStdSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual := rfl

theorem op11_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op11 (native base) (selected base ops) =
      @PDict_RejectionStdSource.core.result.Result.map := rfl

#print axioms op5_installed
#print axioms op6_installed
#print axioms op7_installed
#print axioms op8_installed
#print axioms op9_installed
#print axioms op10_installed
#print axioms op11_installed
end R1Z.PDict_RejectionStd
