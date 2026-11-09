-- Runtime elaboration support: the emitted Option residual reads tag zero.
-- Local scope prevents discriminant collisions in downstream combined imports.
local instance optionDiscriminant {T : Type} : Discriminant (Option T) Isize where
  read_discriminant := fun x => match x with | none => 0#isize | some _ => 1#isize
