import Aeneas
import AspisR1FastDotsCurrent.Types
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1FastDotsCurrent

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::to_limbs]:
    Source: 'crates/aspis-core/src/field/wide_exact.rs', lines 238:4-238:58
    Name pattern: [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::to_limbs]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::to_limbs"]
def aspis_core.field.wide_exact.WideExact.to_limbs
  (self : aspis_core.field.wide_exact.WideExact) :
  Result (Array Std.U32 8#usize)
  := do
  let i := self.c0.c0.a
  let i1 := self.c0.c0.b
  let i2 := self.c0.c1.a
  let i3 := self.c0.c1.b
  let i4 := self.c1.c0.a
  let i5 := self.c1.c0.b
  let i6 := self.c1.c1.a
  let i7 := self.c1.c1.b
  ok (Array.make 8#usize [ i, i1, i2, i3, i4, i5, i6, i7 ])


end AspisR1FastDotsCurrent
