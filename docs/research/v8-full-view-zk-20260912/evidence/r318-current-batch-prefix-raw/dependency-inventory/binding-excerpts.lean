/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B}::mul]:
    Source: '../r110_norm.rs', lines 14:21-19:5 -/
def circle_norm.joined_inverse.line_norm.r110_norm.B.mul
  (self : circle_norm.joined_inverse.line_norm.r110_norm.B)
  (r : circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.B
  := do
  let i ← lift (core.convert.num.FromU64U32.from self)
  let i1 ← lift (core.convert.num.FromU64U32.from r)
  let x ← lift (Std.U64.wrapping_mul i i1)
  let i2 ←
    lift (core.convert.num.FromU64U32.from
      circle_norm.joined_inverse.line_norm.r110_norm.P110)
  let i3 ← lift (x &&& i2)
  let i4 ← lift (Std.U64.wrapping_shr x 31#i32)
  let s ← lift (Std.U64.wrapping_add i3 i4)
  let i5 ←
    lift (core.convert.num.FromU64U32.from
      circle_norm.joined_inverse.line_norm.r110_norm.P110)
  if s >= i5
  then
    let i6 ←
      lift (core.convert.num.FromU64U32.from
        circle_norm.joined_inverse.line_norm.r110_norm.P110)
    let i7 ← lift (Std.U64.wrapping_sub s i6)
    let i8 ← lift (UScalar.cast .U32 i7)
    ok i8
  else let i6 ← lift (UScalar.cast .U32 s)
       ok i6

/-- [core::slice::{[T]}::last]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 281:4-281:42
    Name pattern: [core::slice::{[@T]}::last]
    Visibility: public -/
@[rust_fun "core::slice::{[@T]}::last"]
axiom core.slice.Slice.last {T : Type} : (Slice T) → Result (Option T)
