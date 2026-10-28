import R1Z.ProverRwDictionaryBytes
import R1Z.ProverRwDictionaryOptionSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryOption
open Aeneas Aeneas.Std Result ProverRwFull
namespace Src
abbrev okOr := @ProverRwDictionaryOptionSource.core.option.Option.ok_or
abbrev branch := @ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch
abbrev residual := ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
end Src
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwDictionaryBytes.selected ops with
    op7 := @Src.okOr,op9 := @Src.branch,op10 := Src.residual}

theorem ok_none (ops : ExternalFuns) (T E : Type) (error : E) :
    (selected ops).op7 (none : Option T) error = .ok (.Err error) := rfl

theorem ok_some (ops : ExternalFuns) {T E : Type} (x : T) (error : E) :
    (selected ops).op7 (some x) error = .ok (.Ok x) := rfl

theorem branch_none (ops : ExternalFuns) (T : Type) :
    (selected ops).op9 (none : Option T) =
      .ok (core.ops.control_flow.ControlFlow.Break none) := rfl

theorem branch_some (ops : ExternalFuns) {T : Type} (x : T) :
    (selected ops).op9 (some x) =
      .ok (core.ops.control_flow.ControlFlow.Continue x) := rfl

theorem residual_none (ops : ExternalFuns) (T : Type) :
    (selected ops).op10 T none = .ok none := by
  change Src.residual T none = .ok none
  simp [Src.residual,
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    read_discriminant,ProverRwDictionaryOptionSource.optionDiscriminant]

/-- Infallible has no inhabitants: all residuals are the none branch. -/
theorem residual_all (ops : ExternalFuns) (T : Type) (x : Option core.convert.Infallible) :
    (selected ops).op10 T x = .ok none := by
  cases x with
  | none => exact residual_none ops T
  | some x => cases x

#print axioms ok_none
#print axioms ok_some
#print axioms branch_none
#print axioms branch_some
#print axioms residual_none
#print axioms residual_all
end R1Z.ProverRwDictionaryOption
