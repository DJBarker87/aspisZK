-- Exact generated declaration cuts; bodies unchanged.
import AspisR1CuBorrowOption.Types
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1CuBorrowOption
/-- [aspis_cu_borrow_option::{impl aspis_cu_borrow_option::BorrowTry<'a, T> for core::option::Option<&'a mut T>}::branch]:
    Source: 'lib.rs', lines 7:4-12:5
    Visibility: public -/
def core.option.OptionMutAT.Insts.Aspis_cu_borrow_optionBorrowTry.branch
  {T : Type} (self : Option T) :
  Result ((core.ops.control_flow.ControlFlow (Option core.convert.Infallible)
    T) × (core.ops.control_flow.ControlFlow (Option core.convert.Infallible) T
    → Option T))
  := do
  match self with
  | none =>
    let back := fun cf => none
    ok (core.ops.control_flow.ControlFlow.Break none, back)
  | some v =>
    let back :=
      fun cf =>
        let t :=
          match cf with
          | core.ops.control_flow.ControlFlow.Continue t1 => t1
          | _ => v
        some t
    ok (core.ops.control_flow.ControlFlow.Continue v, back)

/-- [aspis_cu_borrow_option::from_residual]:
    Source: 'lib.rs', lines 14:0-18:5
    Visibility: public -/
def from_residual
  (T : Type) (residual : Option core.convert.Infallible) :
  Result ((Option (Std.Usize × T)) × (Option (Std.Usize × T) → Unit))
  := do
  match residual with
  | none => let back := fun o => ()
            ok (none, back)
  | some _ => fail panic

end AspisR1CuBorrowOption
