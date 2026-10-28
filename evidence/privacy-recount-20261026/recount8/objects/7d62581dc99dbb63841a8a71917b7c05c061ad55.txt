import R1Z.PV_RDB2C_PV_B2_C_RawWeights251Funs
set_option autoImplicit false
-- Component: PV_B2_Total_P.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
abbrev aspis_core.field.M31 := PV_B2_251c1.aspis_core.field.M31
abbrev aspis_core.field.CM31 := PV_B2_251c1.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := PV_B2_251c1.aspis_core.field.QM31
def aspis_core.field.P : Std.U32 := 2147483647#u32
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem P : PV_B2_251c1.aspis_core.field.P = PV_B2_C_251FieldValue.aspis_core.field.P := by
  unfold PV_B2_251c1.aspis_core.field.P PV_B2_C_251FieldValue.aspis_core.field.P
  rfl
#print axioms P
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_ct_subtract_p.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.ct.subtract_p (x : Std.U32) : Std.U32 :=
  let i := (UScalar.cast_fromBool .U32 (x >= aspis_core.field.P))
  let mask := (core.num.U32.wrapping_sub 0#u32 i)
  let i1 := (aspis_core.field.P &&& mask)
  (core.num.U32.wrapping_sub x i1)
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem ct_subtract_p (x : Std.U32) : PV_B2_251c1.aspis_core.field.ct.subtract_p x = ok (PV_B2_C_251FieldValue.aspis_core.field.ct.subtract_p x) := by
  unfold PV_B2_251c1.aspis_core.field.ct.subtract_p PV_B2_C_251FieldValue.aspis_core.field.ct.subtract_p
  simp only [PV_B2_C_251FieldTotal.P,lift,bind_tc_ok]
#print axioms ct_subtract_p
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_ct_reduce64.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.ct.reduce64 (x : Std.U64) : Std.U32 :=
  let i := (UScalar.cast .U64 aspis_core.field.P)
  let i1 := (x &&& i)
  let i2 := (Std.U64.wrapping_shr x 31#u32)
  let x1 := (Std.U64.wrapping_add i1 i2)
  let i3 := (UScalar.cast .U64 aspis_core.field.P)
  let i4 := (x1 &&& i3)
  let i5 := (Std.U64.wrapping_shr x1 31#u32)
  let x2 := (Std.U64.wrapping_add i4 i5)
  let i6 := (UScalar.cast .U32 x2)
  aspis_core.field.ct.subtract_p i6
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem ct_reduce64 (x : Std.U64) : PV_B2_251c1.aspis_core.field.ct.reduce64 x = ok (PV_B2_C_251FieldValue.aspis_core.field.ct.reduce64 x) := by
  unfold PV_B2_251c1.aspis_core.field.ct.reduce64 PV_B2_C_251FieldValue.aspis_core.field.ct.reduce64
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p,lift,bind_tc_ok]
#print axioms ct_reduce64
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_ct_add.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.ct.add (a : Std.U32) (b : Std.U32) : Std.U32 :=
  let i := (core.num.U32.wrapping_add a b)
  aspis_core.field.ct.subtract_p i
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem ct_add (a : Std.U32) (b : Std.U32) : PV_B2_251c1.aspis_core.field.ct.add a b = ok (PV_B2_C_251FieldValue.aspis_core.field.ct.add a b) := by
  unfold PV_B2_251c1.aspis_core.field.ct.add PV_B2_C_251FieldValue.aspis_core.field.ct.add
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64,lift,bind_tc_ok]
#print axioms ct_add
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_ct_sub.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.ct.sub (a : Std.U32) (b : Std.U32) : Std.U32 :=
  let i := (core.num.U32.wrapping_add a aspis_core.field.P)
  let i1 := (core.num.U32.wrapping_sub i b)
  aspis_core.field.ct.subtract_p i1
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem ct_sub (a : Std.U32) (b : Std.U32) : PV_B2_251c1.aspis_core.field.ct.sub a b = ok (PV_B2_C_251FieldValue.aspis_core.field.ct.sub a b) := by
  unfold PV_B2_251c1.aspis_core.field.ct.sub PV_B2_C_251FieldValue.aspis_core.field.ct.sub
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add,lift,bind_tc_ok]
#print axioms ct_sub
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_reduce_u64.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.reduce_u64 (x : Std.U64) : Std.U32 :=
  aspis_core.field.ct.reduce64 x
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem reduce_u64 (x : Std.U64) : PV_B2_251c1.aspis_core.field.reduce_u64 x = ok (PV_B2_C_251FieldValue.aspis_core.field.reduce_u64 x) := by
  unfold PV_B2_251c1.aspis_core.field.reduce_u64 PV_B2_C_251FieldValue.aspis_core.field.reduce_u64
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub,lift,bind_tc_ok]
#print axioms reduce_u64
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_M31_mul.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.M31.mul
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  aspis_core.field.M31
  :=
  let i := (UScalar.cast .U64 self)
  let i1 := (UScalar.cast .U64 rhs)
  let i2 := (Std.U64.wrapping_mul i i1)
  let i3 := aspis_core.field.reduce_u64 i2
  i3
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem M31_mul (self : PV_B2_251c1.aspis_core.field.M31) (rhs : PV_B2_251c1.aspis_core.field.M31) : PV_B2_251c1.aspis_core.field.M31.mul self rhs = ok (PV_B2_C_251FieldValue.aspis_core.field.M31.mul self rhs) := by
  unfold PV_B2_251c1.aspis_core.field.M31.mul PV_B2_C_251FieldValue.aspis_core.field.M31.mul
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub, PV_B2_C_251FieldTotal.reduce_u64,lift,bind_tc_ok]
#print axioms M31_mul
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_M31_reduce_u64.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.M31.reduce_u64
  (value : Std.U64) : aspis_core.field.M31 :=
  let i := aspis_core.field.reduce_u64 value
  i
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem M31_reduce_u64 (value : Std.U64) : PV_B2_251c1.aspis_core.field.M31.reduce_u64 value = ok (PV_B2_C_251FieldValue.aspis_core.field.M31.reduce_u64 value) := by
  unfold PV_B2_251c1.aspis_core.field.M31.reduce_u64 PV_B2_C_251FieldValue.aspis_core.field.M31.reduce_u64
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub, PV_B2_C_251FieldTotal.reduce_u64, PV_B2_C_251FieldTotal.M31_mul,lift,bind_tc_ok]
#print axioms M31_reduce_u64
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_M31_add.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.M31.add
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  aspis_core.field.M31
  :=
  let i := aspis_core.field.ct.add self rhs
  i
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem M31_add (self : PV_B2_251c1.aspis_core.field.M31) (rhs : PV_B2_251c1.aspis_core.field.M31) : PV_B2_251c1.aspis_core.field.M31.add self rhs = ok (PV_B2_C_251FieldValue.aspis_core.field.M31.add self rhs) := by
  unfold PV_B2_251c1.aspis_core.field.M31.add PV_B2_C_251FieldValue.aspis_core.field.M31.add
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub, PV_B2_C_251FieldTotal.reduce_u64, PV_B2_C_251FieldTotal.M31_mul, PV_B2_C_251FieldTotal.M31_reduce_u64,lift,bind_tc_ok]
#print axioms M31_add
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_M31_double.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.M31.double
  (self : aspis_core.field.M31) : aspis_core.field.M31 :=
  aspis_core.field.M31.add self self
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem M31_double (self : PV_B2_251c1.aspis_core.field.M31) : PV_B2_251c1.aspis_core.field.M31.double self = ok (PV_B2_C_251FieldValue.aspis_core.field.M31.double self) := by
  unfold PV_B2_251c1.aspis_core.field.M31.double PV_B2_C_251FieldValue.aspis_core.field.M31.double
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub, PV_B2_C_251FieldTotal.reduce_u64, PV_B2_C_251FieldTotal.M31_mul, PV_B2_C_251FieldTotal.M31_reduce_u64, PV_B2_C_251FieldTotal.M31_add,lift,bind_tc_ok]
#print axioms M31_double
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_CM31_add.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.CM31.add
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  aspis_core.field.CM31
  :=
  let m := aspis_core.field.M31.add self.a rhs.a
  let m1 := aspis_core.field.M31.add self.b rhs.b
  { a := m, b := m1 }
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem CM31_add (self : PV_B2_251c1.aspis_core.field.CM31) (rhs : PV_B2_251c1.aspis_core.field.CM31) : PV_B2_251c1.aspis_core.field.CM31.add self rhs = ok (PV_B2_C_251FieldValue.aspis_core.field.CM31.add self rhs) := by
  unfold PV_B2_251c1.aspis_core.field.CM31.add PV_B2_C_251FieldValue.aspis_core.field.CM31.add
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub, PV_B2_C_251FieldTotal.reduce_u64, PV_B2_C_251FieldTotal.M31_mul, PV_B2_C_251FieldTotal.M31_reduce_u64, PV_B2_C_251FieldTotal.M31_add, PV_B2_C_251FieldTotal.M31_double,lift,bind_tc_ok]
#print axioms CM31_add
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_M31_sub.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.M31.sub
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  aspis_core.field.M31
  :=
  let i := aspis_core.field.ct.sub self rhs
  i
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem M31_sub (self : PV_B2_251c1.aspis_core.field.M31) (rhs : PV_B2_251c1.aspis_core.field.M31) : PV_B2_251c1.aspis_core.field.M31.sub self rhs = ok (PV_B2_C_251FieldValue.aspis_core.field.M31.sub self rhs) := by
  unfold PV_B2_251c1.aspis_core.field.M31.sub PV_B2_C_251FieldValue.aspis_core.field.M31.sub
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub, PV_B2_C_251FieldTotal.reduce_u64, PV_B2_C_251FieldTotal.M31_mul, PV_B2_C_251FieldTotal.M31_reduce_u64, PV_B2_C_251FieldTotal.M31_add, PV_B2_C_251FieldTotal.M31_double, PV_B2_C_251FieldTotal.CM31_add,lift,bind_tc_ok]
#print axioms M31_sub
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_CM31_sub.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.CM31.sub
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  aspis_core.field.CM31
  :=
  let m := aspis_core.field.M31.sub self.a rhs.a
  let m1 := aspis_core.field.M31.sub self.b rhs.b
  { a := m, b := m1 }
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem CM31_sub (self : PV_B2_251c1.aspis_core.field.CM31) (rhs : PV_B2_251c1.aspis_core.field.CM31) : PV_B2_251c1.aspis_core.field.CM31.sub self rhs = ok (PV_B2_C_251FieldValue.aspis_core.field.CM31.sub self rhs) := by
  unfold PV_B2_251c1.aspis_core.field.CM31.sub PV_B2_C_251FieldValue.aspis_core.field.CM31.sub
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub, PV_B2_C_251FieldTotal.reduce_u64, PV_B2_C_251FieldTotal.M31_mul, PV_B2_C_251FieldTotal.M31_reduce_u64, PV_B2_C_251FieldTotal.M31_add, PV_B2_C_251FieldTotal.M31_double, PV_B2_C_251FieldTotal.CM31_add, PV_B2_C_251FieldTotal.M31_sub,lift,bind_tc_ok]
#print axioms CM31_sub
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_CM31_mul.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.CM31.mul
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  aspis_core.field.CM31
  :=
  let m0 := aspis_core.field.M31.mul self.a rhs.a
  let m1 := aspis_core.field.M31.mul self.b rhs.b
  let i := self.a
  let i1 := (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 := (core.convert.num.FromU64U32.from i2)
  let i4 := (Std.U64.wrapping_add i1 i3)
  let i5 := rhs.a
  let i6 := (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 := (core.convert.num.FromU64U32.from i7)
  let i9 := (Std.U64.wrapping_add i6 i8)
  let i10 := (Std.U64.wrapping_mul i4 i9)
  let m2 := aspis_core.field.M31.reduce_u64 i10
  let m := aspis_core.field.M31.sub m0 m1
  let m3 := aspis_core.field.M31.sub m2 m0
  let m4 := aspis_core.field.M31.sub m3 m1
  { a := m, b := m4 }
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem CM31_mul (self : PV_B2_251c1.aspis_core.field.CM31) (rhs : PV_B2_251c1.aspis_core.field.CM31) : PV_B2_251c1.aspis_core.field.CM31.mul self rhs = ok (PV_B2_C_251FieldValue.aspis_core.field.CM31.mul self rhs) := by
  unfold PV_B2_251c1.aspis_core.field.CM31.mul PV_B2_C_251FieldValue.aspis_core.field.CM31.mul
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub, PV_B2_C_251FieldTotal.reduce_u64, PV_B2_C_251FieldTotal.M31_mul, PV_B2_C_251FieldTotal.M31_reduce_u64, PV_B2_C_251FieldTotal.M31_add, PV_B2_C_251FieldTotal.M31_double, PV_B2_C_251FieldTotal.CM31_add, PV_B2_C_251FieldTotal.M31_sub, PV_B2_C_251FieldTotal.CM31_sub,lift,bind_tc_ok]
#print axioms CM31_mul
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_mul_by_r.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.mul_by_r
  (x : aspis_core.field.CM31) : aspis_core.field.CM31 :=
  let m := aspis_core.field.M31.double x.a
  let m1 := aspis_core.field.M31.sub m x.b
  let m2 := aspis_core.field.M31.double x.b
  let m3 := aspis_core.field.M31.add x.a m2
  { a := m1, b := m3 }
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem mul_by_r (x : PV_B2_251c1.aspis_core.field.CM31) : PV_B2_251c1.aspis_core.field.mul_by_r x = ok (PV_B2_C_251FieldValue.aspis_core.field.mul_by_r x) := by
  unfold PV_B2_251c1.aspis_core.field.mul_by_r PV_B2_C_251FieldValue.aspis_core.field.mul_by_r
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub, PV_B2_C_251FieldTotal.reduce_u64, PV_B2_C_251FieldTotal.M31_mul, PV_B2_C_251FieldTotal.M31_reduce_u64, PV_B2_C_251FieldTotal.M31_add, PV_B2_C_251FieldTotal.M31_double, PV_B2_C_251FieldTotal.CM31_add, PV_B2_C_251FieldTotal.M31_sub, PV_B2_C_251FieldTotal.CM31_sub, PV_B2_C_251FieldTotal.CM31_mul,lift,bind_tc_ok]
#print axioms mul_by_r
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_QM31_ZERO.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.QM31.ZERO : aspis_core.field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem QM31_ZERO : PV_B2_251c1.aspis_core.field.QM31.ZERO = PV_B2_C_251FieldValue.aspis_core.field.QM31.ZERO := by
  unfold PV_B2_251c1.aspis_core.field.QM31.ZERO PV_B2_C_251FieldValue.aspis_core.field.QM31.ZERO
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub, PV_B2_C_251FieldTotal.reduce_u64, PV_B2_C_251FieldTotal.M31_mul, PV_B2_C_251FieldTotal.M31_reduce_u64, PV_B2_C_251FieldTotal.M31_add, PV_B2_C_251FieldTotal.M31_double, PV_B2_C_251FieldTotal.CM31_add, PV_B2_C_251FieldTotal.M31_sub, PV_B2_C_251FieldTotal.CM31_sub, PV_B2_C_251FieldTotal.CM31_mul, PV_B2_C_251FieldTotal.mul_by_r,lift,bind_tc_ok]
#print axioms QM31_ZERO
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_QM31_ONE.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.QM31.ONE : aspis_core.field.QM31 :=
  { c0 := { a := 1#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem QM31_ONE : PV_B2_251c1.aspis_core.field.QM31.ONE = PV_B2_C_251FieldValue.aspis_core.field.QM31.ONE := by
  unfold PV_B2_251c1.aspis_core.field.QM31.ONE PV_B2_C_251FieldValue.aspis_core.field.QM31.ONE
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub, PV_B2_C_251FieldTotal.reduce_u64, PV_B2_C_251FieldTotal.M31_mul, PV_B2_C_251FieldTotal.M31_reduce_u64, PV_B2_C_251FieldTotal.M31_add, PV_B2_C_251FieldTotal.M31_double, PV_B2_C_251FieldTotal.CM31_add, PV_B2_C_251FieldTotal.M31_sub, PV_B2_C_251FieldTotal.CM31_sub, PV_B2_C_251FieldTotal.CM31_mul, PV_B2_C_251FieldTotal.mul_by_r, PV_B2_C_251FieldTotal.QM31_ZERO,lift,bind_tc_ok]
#print axioms QM31_ONE
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_QM31_add.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.QM31.add
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  aspis_core.field.QM31
  :=
  let c := aspis_core.field.CM31.add self.c0 rhs.c0
  let c1 := aspis_core.field.CM31.add self.c1 rhs.c1
  { c0 := c, c1 }
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem QM31_add (self : PV_B2_251c1.aspis_core.field.QM31) (rhs : PV_B2_251c1.aspis_core.field.QM31) : PV_B2_251c1.aspis_core.field.QM31.add self rhs = ok (PV_B2_C_251FieldValue.aspis_core.field.QM31.add self rhs) := by
  unfold PV_B2_251c1.aspis_core.field.QM31.add PV_B2_C_251FieldValue.aspis_core.field.QM31.add
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub, PV_B2_C_251FieldTotal.reduce_u64, PV_B2_C_251FieldTotal.M31_mul, PV_B2_C_251FieldTotal.M31_reduce_u64, PV_B2_C_251FieldTotal.M31_add, PV_B2_C_251FieldTotal.M31_double, PV_B2_C_251FieldTotal.CM31_add, PV_B2_C_251FieldTotal.M31_sub, PV_B2_C_251FieldTotal.CM31_sub, PV_B2_C_251FieldTotal.CM31_mul, PV_B2_C_251FieldTotal.mul_by_r, PV_B2_C_251FieldTotal.QM31_ZERO, PV_B2_C_251FieldTotal.QM31_ONE,lift,bind_tc_ok]
#print axioms QM31_add
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_QM31_sub.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.QM31.sub
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  aspis_core.field.QM31
  :=
  let c := aspis_core.field.CM31.sub self.c0 rhs.c0
  let c1 := aspis_core.field.CM31.sub self.c1 rhs.c1
  { c0 := c, c1 }
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem QM31_sub (self : PV_B2_251c1.aspis_core.field.QM31) (rhs : PV_B2_251c1.aspis_core.field.QM31) : PV_B2_251c1.aspis_core.field.QM31.sub self rhs = ok (PV_B2_C_251FieldValue.aspis_core.field.QM31.sub self rhs) := by
  unfold PV_B2_251c1.aspis_core.field.QM31.sub PV_B2_C_251FieldValue.aspis_core.field.QM31.sub
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub, PV_B2_C_251FieldTotal.reduce_u64, PV_B2_C_251FieldTotal.M31_mul, PV_B2_C_251FieldTotal.M31_reduce_u64, PV_B2_C_251FieldTotal.M31_add, PV_B2_C_251FieldTotal.M31_double, PV_B2_C_251FieldTotal.CM31_add, PV_B2_C_251FieldTotal.M31_sub, PV_B2_C_251FieldTotal.CM31_sub, PV_B2_C_251FieldTotal.CM31_mul, PV_B2_C_251FieldTotal.mul_by_r, PV_B2_C_251FieldTotal.QM31_ZERO, PV_B2_C_251FieldTotal.QM31_ONE, PV_B2_C_251FieldTotal.QM31_add,lift,bind_tc_ok]
#print axioms QM31_sub
end PV_B2_C_251FieldTotal

end

-- Component: PV_B2_Total_QM31_mul.lean
section
open Aeneas Aeneas.Std Result
namespace PV_B2_C_251FieldValue
def aspis_core.field.QM31.mul
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  aspis_core.field.QM31
  :=
  let m0 := aspis_core.field.CM31.mul self.c0 rhs.c0
  let m1 := aspis_core.field.CM31.mul self.c1 rhs.c1
  let c := aspis_core.field.CM31.add self.c0 self.c1
  let c1 := aspis_core.field.CM31.add rhs.c0 rhs.c1
  let m2 := aspis_core.field.CM31.mul c c1
  let c2 := aspis_core.field.mul_by_r m1
  let c3 := aspis_core.field.CM31.add m0 c2
  let c4 := aspis_core.field.CM31.sub m2 m0
  let c5 := aspis_core.field.CM31.sub c4 m1
  { c0 := c3, c1 := c5 }
end PV_B2_C_251FieldValue
namespace PV_B2_C_251FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem QM31_mul (self : PV_B2_251c1.aspis_core.field.QM31) (rhs : PV_B2_251c1.aspis_core.field.QM31) : PV_B2_251c1.aspis_core.field.QM31.mul self rhs = ok (PV_B2_C_251FieldValue.aspis_core.field.QM31.mul self rhs) := by
  unfold PV_B2_251c1.aspis_core.field.QM31.mul PV_B2_C_251FieldValue.aspis_core.field.QM31.mul
  simp only [PV_B2_C_251FieldTotal.P, PV_B2_C_251FieldTotal.ct_subtract_p, PV_B2_C_251FieldTotal.ct_reduce64, PV_B2_C_251FieldTotal.ct_add, PV_B2_C_251FieldTotal.ct_sub, PV_B2_C_251FieldTotal.reduce_u64, PV_B2_C_251FieldTotal.M31_mul, PV_B2_C_251FieldTotal.M31_reduce_u64, PV_B2_C_251FieldTotal.M31_add, PV_B2_C_251FieldTotal.M31_double, PV_B2_C_251FieldTotal.CM31_add, PV_B2_C_251FieldTotal.M31_sub, PV_B2_C_251FieldTotal.CM31_sub, PV_B2_C_251FieldTotal.CM31_mul, PV_B2_C_251FieldTotal.mul_by_r, PV_B2_C_251FieldTotal.QM31_ZERO, PV_B2_C_251FieldTotal.QM31_ONE, PV_B2_C_251FieldTotal.QM31_add, PV_B2_C_251FieldTotal.QM31_sub,lift,bind_tc_ok]
#print axioms QM31_mul
end PV_B2_C_251FieldTotal

end

