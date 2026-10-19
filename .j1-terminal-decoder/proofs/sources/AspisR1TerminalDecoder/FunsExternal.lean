import Aeneas
import AspisR1TerminalDecoder.Types

/- The unused opaque Slice.eq template is deliberately not implemented.
This compatibility instance supplies only the builtin Option discriminant.
Exact decoder renamed LLBC (11a42d22...d13da2c), type 20: None = Isize 0,
Some = Isize 1. Aeneas maps this Rust enum to Lean Option. The scoped
instance is active inside the unchanged generated namespace only. -/
open Aeneas Aeneas.Std
namespace AspisR1TerminalDecoder

def optionDiscriminant {α : Type} : Option α → Isize
  | none => 0#isize
  | some _ => 1#isize

scoped instance optionDiscriminantInst {α : Type} : Discriminant (Option α) Isize where
  read_discriminant := optionDiscriminant

theorem optionDiscriminant_none {α : Type} :
    read_discriminant (none : Option α) = 0#isize := rfl

theorem optionDiscriminant_some {α : Type} (x : α) :
    read_discriminant (some x) = 1#isize := rfl

#print axioms optionDiscriminant_none
#print axioms optionDiscriminant_some
end AspisR1TerminalDecoder
