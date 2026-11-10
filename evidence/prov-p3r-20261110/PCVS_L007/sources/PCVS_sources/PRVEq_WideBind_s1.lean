-- PCVS_ item (3): the frozen 4bb3b3f aspis-core WideExact mul / ZERO / ONE emission (PCVS_E001, overflow ON, features r0)
-- against the gate declarations, and the three op17 bindings stated by PRVEq_Op17_p2.
import Aeneas
import PRVEq_Op17_p2
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option autoImplicit false
noncomputable section
namespace PCVS_Fresh
abbrev field.M31 := AspisR1Qm31ArithmeticProbe.field.M31
abbrev field.CM31 := AspisR1Qm31ArithmeticProbe.field.CM31
abbrev field.QM31 := AspisR1Qm31ArithmeticProbe.field.QM31
abbrev field.wide_exact.WideExact := AspisR1CurrentWideMul.field.wide_exact.WideExact
end PCVS_Fresh

namespace PCVS_Fresh

/-- [aspis_core::field::{aspis_core::field::QM31}::ZERO]
    Source: 'crates/aspis-core/src/field.rs', lines 869:4-878:6
    Visibility: public -/
@[global_simps, irreducible]
def field.QM31.ZERO : field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::ZERO]
    Source: 'crates/aspis-core/src/field/wide_exact.rs', lines 41:4-44:6
    Visibility: public -/
@[global_simps, irreducible]
def field.wide_exact.WideExact.ZERO : field.wide_exact.WideExact :=
  { c0 := field.QM31.ZERO, c1 := field.QM31.ZERO }

/-- [aspis_core::field::{aspis_core::field::QM31}::ONE]
    Source: 'crates/aspis-core/src/field.rs', lines 879:4-888:6
    Visibility: public -/
@[global_simps, irreducible]
def field.QM31.ONE : field.QM31 :=
  { c0 := { a := 1#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::ONE]
    Source: 'crates/aspis-core/src/field/wide_exact.rs', lines 45:4-48:6
    Visibility: public -/
@[global_simps, irreducible]
def field.wide_exact.WideExact.ONE : field.wide_exact.WideExact :=
  { c0 := field.QM31.ONE, c1 := field.QM31.ZERO }

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::{aspis_core::field::M31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 62:4-88:5
    Visibility: public -/
def field.M31.add (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let s ← self + rhs
  if s >= field.P
  then let s1 ← s - field.P
       ok s1
  else ok s

/-- [aspis_core::field::{aspis_core::field::M31}::double]:
    Source: 'crates/aspis-core/src/field.rs', lines 183:4-185:5
    Visibility: public -/
def field.M31.double (self : field.M31) : Result field.M31 := do
  field.M31.add self self

/-- [aspis_core::field::{aspis_core::field::M31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 94:4-119:5
    Visibility: public -/
def field.M31.sub (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← self + field.P
  let s ← i - rhs
  if s >= field.P
  then let s1 ← s - field.P
       ok s1
  else ok s

/-- [aspis_core::field::mul_by_r]:
    Source: 'crates/aspis-core/src/field.rs', lines 860:0-866:1 -/
def field.mul_by_r (x : field.CM31) : Result field.CM31 := do
  let m ← field.M31.double x.a
  let m1 ← field.M31.sub m x.b
  let m2 ← field.M31.double x.b
  let m3 ← field.M31.add x.a m2
  ok { a := m1, b := m3 }

/-- [aspis_core::field::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 31:0-44:1 -/
def field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 field.P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= field.P
  then x3 - field.P
  else ok x3

/-- [aspis_core::field::{aspis_core::field::M31}::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 153:4-155:5
    Visibility: public -/
def field.M31.reduce_u64 (value : Std.U64) : Result field.M31 := do
  let i ← field.reduce_u64 value
  ok i

/-- [aspis_core::field::{aspis_core::field::M31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 133:4-137:5
    Visibility: public -/
def field.M31.mul (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← i * i1
  let i3 ← field.reduce_u64 i2
  ok i3

/-- [aspis_core::field::{aspis_core::field::CM31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 306:4-320:5
    Visibility: public -/
def field.CM31.mul
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m0 ← field.M31.mul self.a rhs.a
  let m1 ← field.M31.mul self.b rhs.b
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 := rhs.a
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 ← lift (core.convert.num.FromU64U32.from i7)
  let i9 ← i6 + i8
  let i10 ← i4 * i9
  let m2 ← field.M31.reduce_u64 i10
  let m ← field.M31.sub m0 m1
  let m3 ← field.M31.sub m2 m0
  let m4 ← field.M31.sub m3 m1
  ok { a := m, b := m4 }

/-- [aspis_core::field::{aspis_core::field::CM31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 289:4-294:5
    Visibility: public -/
def field.CM31.sub
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.sub self.a rhs.a
  let m1 ← field.M31.sub self.b rhs.b
  ok { a := m, b := m1 }

/-- [aspis_core::field::{aspis_core::field::CM31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 281:4-286:5
    Visibility: public -/
def field.CM31.add
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.add self.a rhs.a
  let m1 ← field.M31.add self.b rhs.b
  ok { a := m, b := m1 }

/-- [aspis_core::field::{aspis_core::field::QM31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 935:4-945:5
    Visibility: public -/
def field.QM31.mul
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let m0 ← field.CM31.mul self.c0 rhs.c0
  let m1 ← field.CM31.mul self.c1 rhs.c1
  let c ← field.CM31.add self.c0 self.c1
  let c1 ← field.CM31.add rhs.c0 rhs.c1
  let m2 ← field.CM31.mul c c1
  let c2 ← field.mul_by_r m1
  let c3 ← field.CM31.add m0 c2
  let c4 ← field.CM31.sub m2 m0
  let c5 ← field.CM31.sub c4 m1
  ok { c0 := c3, c1 := c5 }

/-- [aspis_core::field::{aspis_core::field::QM31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 906:4-913:5
    Visibility: public -/
def field.QM31.sub
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let c ← field.CM31.sub self.c0 rhs.c0
  let c1 ← field.CM31.sub self.c1 rhs.c1
  ok { c0 := c, c1 }

/-- [aspis_core::field::{aspis_core::field::QM31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 896:4-903:5
    Visibility: public -/
def field.QM31.add
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let c ← field.CM31.add self.c0 rhs.c0
  let c1 ← field.CM31.add self.c1 rhs.c1
  ok { c0 := c, c1 }

/-- [aspis_core::field::wide_exact::mul_u]:
    Source: 'crates/aspis-core/src/field/wide_exact.rs', lines 299:0-304:1 -/
def field.wide_exact.mul_u (value : field.QM31) : Result field.QM31 := do
  let c ← field.mul_by_r value.c1
  ok { c0 := c, c1 := value.c0 }

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::mul]:
    Source: 'crates/aspis-core/src/field/wide_exact.rs', lines 112:4-126:5
    Visibility: public -/
def field.wide_exact.WideExact.mul
  (self : field.wide_exact.WideExact) (rhs : field.wide_exact.WideExact) :
  Result field.wide_exact.WideExact
  := do
  let ac ← field.QM31.mul self.c0 rhs.c0
  let bd ← field.QM31.mul self.c1 rhs.c1
  let q ← field.QM31.add self.c0 self.c1
  let q1 ← field.QM31.add rhs.c0 rhs.c1
  let cross ← field.QM31.mul q q1
  let q2 ← field.wide_exact.mul_u bd
  let q3 ← field.QM31.add ac q2
  let q4 ← field.QM31.sub cross ac
  let q5 ← field.QM31.sub q4 bd
  ok { c0 := q3, c1 := q5 }

end PCVS_Fresh

namespace PCVS_Eq
theorem eq_0 : @PCVS_Fresh.field.P = @AspisR1Qm31ArithmeticProbe.field.P := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_1 : @PCVS_Fresh.field.reduce_u64 = @AspisR1Qm31ArithmeticProbe.field.reduce_u64 := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_2 : @PCVS_Fresh.field.M31.add = @AspisR1Qm31ArithmeticProbe.field.M31.add := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_3 : @PCVS_Fresh.field.M31.double = @AspisR1Qm31ArithmeticProbe.field.M31.double := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_4 : @PCVS_Fresh.field.M31.sub = @AspisR1Qm31ArithmeticProbe.field.M31.sub := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_5 : @PCVS_Fresh.field.M31.reduce_u64 = @AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_6 : @PCVS_Fresh.field.M31.mul = @AspisR1Qm31ArithmeticProbe.field.M31.mul := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_7 : @PCVS_Fresh.field.mul_by_r = @AspisR1Qm31ArithmeticProbe.field.mul_by_r := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_8 : @PCVS_Fresh.field.CM31.add = @AspisR1Qm31ArithmeticProbe.field.CM31.add := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_9 : @PCVS_Fresh.field.CM31.sub = @AspisR1Qm31ArithmeticProbe.field.CM31.sub := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_10 : @PCVS_Fresh.field.CM31.mul = @AspisR1Qm31ArithmeticProbe.field.CM31.mul := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_11 : @PCVS_Fresh.field.QM31.add = @AspisR1Qm31ArithmeticProbe.field.QM31.add := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_12 : @PCVS_Fresh.field.QM31.mul = @AspisR1Qm31ArithmeticProbe.field.QM31.mul := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_13 : @PCVS_Fresh.field.QM31.sub = @AspisR1CurrentWideMul.field.QM31.sub := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_14 : @PCVS_Fresh.field.wide_exact.mul_u = @AspisR1CurrentWideMul.field.wide_exact.mul_u := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
theorem eq_15 : @PCVS_Fresh.field.wide_exact.WideExact.mul = @AspisR1CurrentWideMul.field.wide_exact.WideExact.mul := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)

open AspisR1PowersConcreteMul in
def toF (x : AspisR1LoopPowers.field.WideExact) : AspisR1CurrentWideMul.field.wide_exact.WideExact := toWide (AspisR1LoopPowers.toOld x)
open AspisR1PowersConcreteMul in
def fromF (x : AspisR1CurrentWideMul.field.wide_exact.WideExact) : AspisR1LoopPowers.field.WideExact := AspisR1LoopPowers.fromOld (fromWide x)

/-- binding 1: the frozen WideExact::mul (fresh emission), transported by the nominal port, is the gate field.WideExact.mul used by op17. -/
theorem bind_mul (x y : AspisR1LoopPowers.field.WideExact) :
    (do let z ← PCVS_Fresh.field.wide_exact.WideExact.mul (toF x) (toF y); ok (fromF z)) = AspisR1LoopPowers.field.WideExact.mul x y := by
  rw [eq_15]
  unfold AspisR1LoopPowers.field.WideExact.mul AspisR1PowersConcreteMul.sourceMul fromF toF
  rfl

/-- binding 2: frozen WideExact::ZERO. -/
theorem bind_zero : fromF PCVS_Fresh.field.wide_exact.WideExact.ZERO = AspisR1LoopPowers.field.WideExact.ZERO := by
  with_unfolding_all rfl

/-- binding 3: frozen WideExact::ONE. -/
theorem bind_one : fromF PCVS_Fresh.field.wide_exact.WideExact.ONE = AspisR1LoopPowers.field.WideExact.ONE := by
  with_unfolding_all rfl

end PCVS_Eq
#print axioms PCVS_Eq.eq_0
#print axioms PCVS_Eq.eq_1
#print axioms PCVS_Eq.eq_2
#print axioms PCVS_Eq.eq_3
#print axioms PCVS_Eq.eq_4
#print axioms PCVS_Eq.eq_5
#print axioms PCVS_Eq.eq_6
#print axioms PCVS_Eq.eq_7
#print axioms PCVS_Eq.eq_8
#print axioms PCVS_Eq.eq_9
#print axioms PCVS_Eq.eq_10
#print axioms PCVS_Eq.eq_11
#print axioms PCVS_Eq.eq_12
#print axioms PCVS_Eq.eq_13
#print axioms PCVS_Eq.eq_14
#print axioms PCVS_Eq.eq_15
#print axioms PCVS_Eq.bind_mul
#print axioms PCVS_Eq.bind_zero
#print axioms PCVS_Eq.bind_one
