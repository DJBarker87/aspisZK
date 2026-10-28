import Aeneas
set_option autoImplicit false
namespace R1Z.PV_CB_OptionDiscriminant
open Aeneas Aeneas.Std

/-- Logical Rust enum tags, as in the already checked op71 residual adapter. -/
instance optionDiscriminant {T : Type} : Discriminant (Option T) Isize where
  read_discriminant := fun x => match x with | none => 0#isize | some _ => 1#isize

theorem none_tag (T : Type) : read_discriminant (none : Option T) = 0#isize := rfl
theorem some_tag {T : Type} (x : T) : read_discriminant (some x) = 1#isize := rfl

#print axioms none_tag
#print axioms some_tag
end R1Z.PV_CB_OptionDiscriminant
