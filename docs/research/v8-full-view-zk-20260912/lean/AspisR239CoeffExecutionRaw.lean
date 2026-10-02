import AspisR221NormExecutionRaw
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze AspisR221NormExecutionRaw
set_option autoImplicit false
namespace AspisR239CoeffExecutionRaw

def circle_norm.Coeff := Array aspis_core.field.CM31 5#usize
def circle_norm.joined_inverse.line_norm.LineCoeff :=
  Array aspis_core.field.CM31 5#usize

def circle_norm.Coeff.new
  (a : Array aspis_core.field.QM31 3#usize) : Result circle_norm.Coeff := do
  let a1 ← Array.index_usize a 0#usize
  let b ← Array.index_usize a 1#usize
  let c ← Array.index_usize a 2#usize
  let nc ← circle_norm.norm c
  let c1 ← circle_norm.norm a1
  let c2 ← aspis_core.field.CM31.add c1 nc
  let c3 ← circle_norm.norm b
  let c4 ← aspis_core.field.CM31.sub c3 nc
  let c5 ← circle_norm.polar a1 b
  let c6 ← circle_norm.polar a1 c
  let c7 ← circle_norm.polar b c
  ok (Array.make 5#usize [ c2, c4, c5, c6, c7 ])

def aspis_core.field.CM31.mul_m31
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.CM31
  := do
  let m ← aspis_core.field.M31.mul self.a rhs
  let m1 ← aspis_core.field.M31.mul self.b rhs
  ok { a := m, b := m1 }

def circle_norm.Coeff.four
  (self : circle_norm.Coeff) (x : aspis_core.field.M31)
  (y : aspis_core.field.M31) :
  Result (Array aspis_core.field.CM31 4#usize)
  := do
  let c ← Array.index_usize self 0#usize
  let c1 ← Array.index_usize self 1#usize
  let m ← aspis_core.field.M31.mul x x
  let c2 ← aspis_core.field.CM31.mul_m31 c1 m
  let even ← aspis_core.field.CM31.add c c2
  let c3 ← Array.index_usize self 2#usize
  let odd_x ← aspis_core.field.CM31.mul_m31 c3 x
  let c4 ← Array.index_usize self 3#usize
  let odd_y ← aspis_core.field.CM31.mul_m31 c4 y
  let c5 ← Array.index_usize self 4#usize
  let m1 ← aspis_core.field.M31.mul x y
  let cross ← aspis_core.field.CM31.mul_m31 c5 m1
  let positive ← aspis_core.field.CM31.add even odd_x
  let negative ← aspis_core.field.CM31.sub even odd_x
  let plus ← aspis_core.field.CM31.add odd_y cross
  let minus ← aspis_core.field.CM31.sub odd_y cross
  let c6 ← aspis_core.field.CM31.add positive plus
  let c7 ← aspis_core.field.CM31.sub positive plus
  let c8 ← aspis_core.field.CM31.sub negative minus
  let c9 ← aspis_core.field.CM31.add negative minus
  ok (Array.make 4#usize [ c6, c7, c8, c9 ])

def aspis_core.field.M31.half
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  let i ← lift (Std.U32.wrapping_shr self 1#u32)
  let i1 ← lift (self &&& 1#u32)
  let i2 ← lift (Std.U32.wrapping_shl i1 30#u32)
  let i3 ← lift (i ||| i2)
  ok i3

def aspis_core.field.CM31.half
  (self : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  let m ← aspis_core.field.M31.half self.a
  let m1 ← aspis_core.field.M31.half self.b
  ok { a := m, b := m1 }

def circle_norm.joined_inverse.line_norm.LineCoeff.new
  (abc : Array aspis_core.field.QM31 3#usize) :
  Result circle_norm.joined_inverse.line_norm.LineCoeff
  := do
  let c ← circle_norm.Coeff.new abc
  let c1 ← Array.index_usize c 1#usize
  let half ← aspis_core.field.CM31.half c1
  let c2 ← Array.index_usize c 0#usize
  let c3 ← aspis_core.field.CM31.add c2 half
  let c4 ← Array.index_usize c 2#usize
  let c5 ← Array.index_usize c 3#usize
  let c6 ← Array.index_usize c 4#usize
  ok (Array.make 5#usize [ c3, half, c4, c5, c6 ])

def circle_norm.joined_inverse.line_norm.LineCoeff.four
  (self : circle_norm.joined_inverse.line_norm.LineCoeff)
  (x : aspis_core.field.M31) (y : aspis_core.field.M31)
  (t : aspis_core.field.M31) :
  Result (Array aspis_core.field.CM31 4#usize)
  := do
  let c ← Array.index_usize self 0#usize
  let c1 ← Array.index_usize self 1#usize
  let c2 ← aspis_core.field.CM31.mul_m31 c1 t
  let even ← aspis_core.field.CM31.add c c2
  let c3 ← Array.index_usize self 2#usize
  let odd_x ← aspis_core.field.CM31.mul_m31 c3 x
  let c4 ← Array.index_usize self 3#usize
  let odd_y ← aspis_core.field.CM31.mul_m31 c4 y
  let c5 ← Array.index_usize self 4#usize
  let m ← aspis_core.field.M31.mul x y
  let cross ← aspis_core.field.CM31.mul_m31 c5 m
  let positive ← aspis_core.field.CM31.add even odd_x
  let negative ← aspis_core.field.CM31.sub even odd_x
  let plus ← aspis_core.field.CM31.add odd_y cross
  let minus ← aspis_core.field.CM31.sub odd_y cross
  let c6 ← aspis_core.field.CM31.add positive plus
  let c7 ← aspis_core.field.CM31.sub positive plus
  let c8 ← aspis_core.field.CM31.sub negative minus
  let c9 ← aspis_core.field.CM31.add negative minus
  ok (Array.make 4#usize [ c6, c7, c8, c9 ])

/-- Literal API adaptation: both signed source counts and unsigned API counts
encode the same nonnegative integer and therefore the same low five bits. -/
theorem count_one : (1#i32 : I32).bv.toNat = (1#u32 : U32).val := by decide
theorem count_thirty : (30#i32 : I32).bv.toNat = (30#u32 : U32).val := by decide

#print axioms circle_norm.Coeff.new
#print axioms aspis_core.field.CM31.mul_m31
#print axioms circle_norm.Coeff.four
#print axioms aspis_core.field.M31.half
#print axioms aspis_core.field.CM31.half
#print axioms circle_norm.joined_inverse.line_norm.LineCoeff.new
#print axioms circle_norm.joined_inverse.line_norm.LineCoeff.four
#print axioms count_one
#print axioms count_thirty
end AspisR239CoeffExecutionRaw
