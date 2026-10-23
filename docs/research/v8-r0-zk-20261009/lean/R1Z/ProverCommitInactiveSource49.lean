import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1InactiveOwner49

/-- [simulator_inactive_owner49::owned::MASKS]
    Source: 'lib.rs', lines 2:0-8:2
    Visibility: public -/
@[global_simps, irreducible]
def owned.MASKS : Array Std.U16 64#usize :=
  Array.make 64#usize [
    6144#u16, 6144#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6144#u16, 4097#u16, 2048#u16,
    6145#u16, 2049#u16, 2048#u16, 6145#u16, 2049#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 4097#u16, 6145#u16, 6145#u16,
    4097#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16,
    1749#u16
    ]

/-- [simulator_inactive_owner49::owned::row]:
    Source: 'lib.rs', lines 9:0-11:1
    Visibility: public -/
def owned.row (j : Std.Usize) : Result Std.Usize := do
  let i ← j / 64#usize
  let i1 ← i % 4#usize
  let i2 ← j / 256#usize
  let i3 ← i2 % 4#usize
  let i4 ← lift (Std.Usize.wrapping_mul 4#usize i3)
  let i5 ← lift (Std.Usize.wrapping_add i1 i4)
  let i6 ← j / 16#usize
  let i7 ← i6 % 4#usize
  let i8 ← lift (Std.Usize.wrapping_mul 16#usize i7)
  let i9 ← lift (Std.Usize.wrapping_add i5 i8)
  let i10 ← j % 4#usize
  let i11 ← lift (Std.Usize.wrapping_mul 64#usize i10)
  let i12 ← lift (Std.Usize.wrapping_add i9 i11)
  let i13 ← j / 4#usize
  let i14 ← i13 % 4#usize
  let i15 ← lift (Std.Usize.wrapping_mul 256#usize i14)
  ok (Std.Usize.wrapping_add i12 i15)

/-- [simulator_inactive_owner49::owned::inactive]:
    Source: 'lib.rs', lines 12:0-14:1
    Visibility: public -/
def owned.inactive (j : Std.Usize) : Result Bool := do
  let r ← owned.row j
  let i ← r / 16#usize
  let i1 ← Array.index_usize owned.MASKS i
  let i2 ← r % 16#usize
  let i3 ← lift (UScalar.cast .U32 i2)
  let i4 ← lift (Std.U16.wrapping_shr i1 i3)
  let i5 ← lift (i4 &&& 1#u16)
  ok (i5 = 0#u16)

end AspisR1InactiveOwner49
