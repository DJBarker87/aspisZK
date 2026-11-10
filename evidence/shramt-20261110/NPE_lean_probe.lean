import Aeneas
open Aeneas Aeneas.Std Result
-- NPE_: library signatures and definitions of the pinned Aeneas Std used by the gate.
#check @Aeneas.Std.Usize.wrapping_shr
#check @Aeneas.Std.Usize.wrapping_shl
#print Aeneas.Std.Usize.wrapping_shr
#print Aeneas.Std.Usize.wrapping_shl
#print Aeneas.Std.UScalar.wrapping_shr
#print Aeneas.Std.UScalar.wrapping_shl
#print Aeneas.Std.IScalar.hcast
#print Aeneas.Std.UScalar.cast
#print Aeneas.Std.UScalar.shiftRight
#print Aeneas.Std.UScalar.shiftLeft
#print Aeneas.Std.UScalar.shiftRight_UScalar
#print Aeneas.Std.UScalar.shiftRight_IScalar
#print Aeneas.Std.UScalar.shiftLeft_UScalar
#print Aeneas.Std.UScalar.shiftLeft_IScalar
#print Aeneas.Std.UScalarTy.numBits
#print Aeneas.Std.Usize.numBits
#synth HShiftRight Usize Usize (Result Usize)
#synth HShiftRight Usize I32 (Result Usize)
#synth HShiftRight Usize U32 (Result Usize)
#check @Aeneas.Std.IScalar.hcast_val_eq
#check @Aeneas.Std.UScalar.cast_val_eq
#check @Aeneas.Std.IScalar.hcast_bv_eq
-- concrete evaluations (kernel-decided by rfl; tiny terms)
example : IScalar.hcast .U32 (9#i32) = 9#u32 := by rfl
example : (IScalar.hcast .U32 (-1#i32)).val = 4294967295 := by decide
example : (IScalar.hcast .U32 (-55#i32)).val = 4294967241 := by decide
example : (IScalar.hcast .U32 (40#i32)).val = 40 := by decide
example : (UScalar.cast .U32 (9#usize)).val = 9 := by decide
