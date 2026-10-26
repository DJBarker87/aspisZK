import R1Z.PDict_RemainingCommute231_36
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_RejectionStd in

theorem stage37 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_RejectionStd.native base)) :
    PDict_RejectionStd.selected base (@replace (PDict_RejectionStd.native base) ops other) =
    @replace (PDict_RejectionStd.native base) (PDict_RejectionStd.selected base ops) other := by
  letI : ExternalTypes := PDict_RejectionStd.native base
  let upd (d : @ExternalFuns (PDict_RejectionStd.native base)) : @ExternalFuns (PDict_RejectionStd.native base) :=
    { d with
    op5 := PDict_RejectionStdSource.core.option.Option.is_some_and
    op6 := PDict_RejectionStdSource.core.option.Option.as_ref
    op7 := PDict_RejectionStdSource.core.option.Option.ok_or
    op8 := PDict_RejectionStdSource.core.option.Option.Insts.CoreCmpPartialEqOption.eq
    op9 := PDict_RejectionStdSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch
    op10 := PDict_RejectionStdSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    op11 := PDict_RejectionStdSource.core.result.Result.map
  }
  have hu (d : @ExternalFuns (PDict_RejectionStd.native base)) :
      upd (@replace (PDict_RejectionStd.native base) d other) = @replace (PDict_RejectionStd.native base) (upd d) other := by rfl
  change upd (PDict_FileCarrier.selected base (@replace (PDict_RejectionStd.native base) ops other)) =
    @replace (PDict_RejectionStd.native base) (upd (PDict_FileCarrier.selected base ops)) other
  exact (congrArg upd (stage36 base ops other)).trans (hu (PDict_FileCarrier.selected base ops))

#print axioms stage37
end R1Z.PDict_RemainingCommute231
