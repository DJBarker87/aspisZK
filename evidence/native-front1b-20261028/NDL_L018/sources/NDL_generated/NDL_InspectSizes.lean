import Aeneas
open Aeneas Aeneas.Std
#print UScalar.size_def
#print Usize.size_def
#print Usize.numBits_def
#print UScalar.add
#print UScalar.instHAdd
#print Usize.wrapping_add_val_eq
example (x y : Usize) : x+y = UScalar.add x y := rfl
