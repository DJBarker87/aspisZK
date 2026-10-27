import R1Z.ProverRwSuccessHeapInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessErrorSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
def r1_wire.Error.Insts.CoreCmpPartialEqError.eq
  (self : r1_wire.Error) (other : r1_wire.Error) : Result Bool := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  if self1 = other1
  then
    match self with
    | r1_wire.Error.Allocation => ok true
    | r1_wire.Error.RowOrder __self_0 __self_1 =>
      match other with
      | r1_wire.Error.Allocation => ok true
      | r1_wire.Error.RowOrder __arg1_0 __arg1_1 =>
        let b ← lift (core.cmp.impls.PartialEqU8.eq __self_0 __arg1_0)
        if b
        then lift (core.cmp.impls.PartialEqU8.eq __self_1 __arg1_1)
        else ok false
      | r1_wire.Error.InvalidRow => ok true
      | r1_wire.Error.Tag _ => ok true
      | r1_wire.Error.Length _ => ok true
      | r1_wire.Error.NonCanonical _ _ => ok true
      | r1_wire.Error.Boundary _ => ok true
      | r1_wire.Error.Terminal => ok true
      | r1_wire.Error.EqualCirclePoints => ok true
      | r1_wire.Error.TrailingBytes => ok true
      | r1_wire.Error.Public => ok true
      | r1_wire.Error.ActivePole => ok true
    | r1_wire.Error.InvalidRow => ok true
    | r1_wire.Error.Tag __self_0 =>
      match other with
      | r1_wire.Error.Allocation => ok true
      | r1_wire.Error.RowOrder _ _ => ok true
      | r1_wire.Error.InvalidRow => ok true
      | r1_wire.Error.Tag __arg1_0 =>
        lift (core.cmp.impls.PartialEqU8.eq __self_0 __arg1_0)
      | r1_wire.Error.Length _ => ok true
      | r1_wire.Error.NonCanonical _ _ => ok true
      | r1_wire.Error.Boundary _ => ok true
      | r1_wire.Error.Terminal => ok true
      | r1_wire.Error.EqualCirclePoints => ok true
      | r1_wire.Error.TrailingBytes => ok true
      | r1_wire.Error.Public => ok true
      | r1_wire.Error.ActivePole => ok true
    | r1_wire.Error.Length __self_0 =>
      match other with
      | r1_wire.Error.Allocation => ok true
      | r1_wire.Error.RowOrder _ _ => ok true
      | r1_wire.Error.InvalidRow => ok true
      | r1_wire.Error.Tag _ => ok true
      | r1_wire.Error.Length __arg1_0 =>
        lift (core.cmp.impls.PartialEqU8.eq __self_0 __arg1_0)
      | r1_wire.Error.NonCanonical _ _ => ok true
      | r1_wire.Error.Boundary _ => ok true
      | r1_wire.Error.Terminal => ok true
      | r1_wire.Error.EqualCirclePoints => ok true
      | r1_wire.Error.TrailingBytes => ok true
      | r1_wire.Error.Public => ok true
      | r1_wire.Error.ActivePole => ok true
    | r1_wire.Error.NonCanonical __self_0 __self_1 =>
      match other with
      | r1_wire.Error.Allocation => ok true
      | r1_wire.Error.RowOrder _ _ => ok true
      | r1_wire.Error.InvalidRow => ok true
      | r1_wire.Error.Tag _ => ok true
      | r1_wire.Error.Length _ => ok true
      | r1_wire.Error.NonCanonical __arg1_0 __arg1_1 =>
        let b ← lift (core.cmp.impls.PartialEqU8.eq __self_0 __arg1_0)
        if b
        then lift (core.cmp.impls.PartialEqUsize.eq __self_1 __arg1_1)
        else ok false
      | r1_wire.Error.Boundary _ => ok true
      | r1_wire.Error.Terminal => ok true
      | r1_wire.Error.EqualCirclePoints => ok true
      | r1_wire.Error.TrailingBytes => ok true
      | r1_wire.Error.Public => ok true
      | r1_wire.Error.ActivePole => ok true
    | r1_wire.Error.Boundary __self_0 =>
      match other with
      | r1_wire.Error.Allocation => ok true
      | r1_wire.Error.RowOrder _ _ => ok true
      | r1_wire.Error.InvalidRow => ok true
      | r1_wire.Error.Tag _ => ok true
      | r1_wire.Error.Length _ => ok true
      | r1_wire.Error.NonCanonical _ _ => ok true
      | r1_wire.Error.Boundary __arg1_0 =>
        lift (core.cmp.impls.PartialEqUsize.eq __self_0 __arg1_0)
      | r1_wire.Error.Terminal => ok true
      | r1_wire.Error.EqualCirclePoints => ok true
      | r1_wire.Error.TrailingBytes => ok true
      | r1_wire.Error.Public => ok true
      | r1_wire.Error.ActivePole => ok true
    | r1_wire.Error.Terminal => ok true
    | r1_wire.Error.EqualCirclePoints => ok true
    | r1_wire.Error.TrailingBytes => ok true
    | r1_wire.Error.Public => ok true
    | r1_wire.Error.ActivePole => ok true
  else ok false
end R1Z.ProverRwSuccessErrorSource
