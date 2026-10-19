import AspisR1CuBorrowOption.Operations

/-! Name/layout adapters for the concrete Option borrow operations. The only
generalization is a residual None with no returned borrow; the selected pair
specialization is definitionally the unchanged emitted function. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CuIterator

abbrev core.option.Option.Insts.CoreOpsTry_traitTry.branch :=
  @AspisR1CuBorrowOption.core.option.OptionMutAT.Insts.Aspis_cu_borrow_optionBorrowTry.branch

def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    (T : Type) (residual : Option Aeneas.Std.core.convert.Infallible) :
    Result (Option T × (Option T → Unit)) :=
  match residual with
  | none => .ok (none,fun _ => ())
  | some _ => .fail .panic

theorem residual_specialization (T : Type) (r : Option Aeneas.Std.core.convert.Infallible) :
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      (Usize × T) r = AspisR1CuBorrowOption.from_residual T r := by
  cases r <;> rfl

#print axioms residual_specialization
end AspisR1CuIterator
