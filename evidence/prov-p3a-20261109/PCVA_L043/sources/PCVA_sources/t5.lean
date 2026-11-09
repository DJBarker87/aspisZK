import Aeneas
open Aeneas Aeneas.Std Result ControlFlow
set_option pp.proofs false
#print Aeneas.Std.Array.index_usize
#print Aeneas.Std.Array.to_slice
#print Aeneas.Std.Slice.len
#check @Aeneas.Std.Usize.add_spec
#check @Aeneas.Std.UScalar.add_equiv
#print Aeneas.Std.Usize.add
#check @Aeneas.Std.Array.length
#check @Aeneas.Std.Usize.ofNat
#check @Aeneas.Std.Usize.size_eq
#check @Aeneas.Std.Usize.numBits_eq
