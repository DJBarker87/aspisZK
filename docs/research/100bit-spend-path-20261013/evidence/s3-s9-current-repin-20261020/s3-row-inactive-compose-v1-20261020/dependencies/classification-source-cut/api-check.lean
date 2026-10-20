import AspisR1S3InactiveSource.Funs
open Aeneas Aeneas.Std Result WP
#check UScalar.div_spec
#check UScalar.rem_spec
#check UScalar.ShiftRight_spec
#check UScalar.and_spec
#check Array.index_usize_spec
#check UScalar.eq_of_val_eq
#check (fun (x : UScalar UScalarTy.U16) => x = 0#u16)
#print AspisR1S3InactiveSource.r0.opening.inactive
#print axioms AspisR1S3InactiveSource.r0.opening.inactive
