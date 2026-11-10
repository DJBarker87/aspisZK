import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
#check @Aeneas.Std.Usize.wrapping_shr
#check @Aeneas.Std.U64.wrapping_shr
#check @Aeneas.Std.IScalar.hcast
#check @Aeneas.Std.IScalar.cast
#check @Aeneas.Std.UScalar.cast
#check @Aeneas.Std.Usize.wrapping_shl
#check @Aeneas.Std.Usize.wrapping_shr_val_eq
#print Aeneas.Std.Usize.wrapping_shr
#check @Aeneas.Std.UScalar.wrapping_shr
example : IScalar.hcast .U32 (9#i32) = 9#u32 := by rfl
example : UScalar.cast .U32 (9#usize) = 9#u32 := by rfl
