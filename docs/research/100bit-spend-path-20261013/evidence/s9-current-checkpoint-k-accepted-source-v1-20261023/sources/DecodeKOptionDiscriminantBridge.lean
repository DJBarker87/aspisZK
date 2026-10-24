import Aeneas

open Aeneas Aeneas.Std

namespace AspisR1DecodeKHelperV7Bridge

/-- The standard Rust `Option` discriminant encoding, specialized to the
    uninhabited residual payload used by `Option`'s `FromResidual` impl. -/
def optionInfallibleDiscriminant
    (o : Option Aeneas.Std.core.convert.Infallible) : Aeneas.Std.Isize :=
  match o with
  | none => 0#isize
  | some impossible => nomatch impossible

instance optionInfallibleDiscriminantInst :
    Aeneas.Std.Discriminant
      (Option Aeneas.Std.core.convert.Infallible) Aeneas.Std.Isize where
  read_discriminant := optionInfallibleDiscriminant

#print axioms optionInfallibleDiscriminant

end AspisR1DecodeKHelperV7Bridge
