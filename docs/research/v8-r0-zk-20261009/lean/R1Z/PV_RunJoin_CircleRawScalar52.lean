import Aeneas
import R1Z.PV_AL_ShiftLiterals
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleRawScalar52


abbrev field.M31 := U32

def field.P : Std.U32 := 2147483647#u32

def field.ct.subtract_p (x : Std.U32) : Result Std.U32 := do
  let i ← lift (UScalar.cast_fromBool .U32 (x >= field.P))
  let mask ← lift (core.num.U32.wrapping_sub 0#u32 i)
  let i1 ← lift (field.P &&& mask)
  ok (core.num.U32.wrapping_sub x i1)

def field.ct.reduce64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 field.P)
  let i1 ← lift (x &&& i)
  let i2 ← lift (Std.U64.wrapping_shr x 31#u32)
  let x1 ← lift (Std.U64.wrapping_add i1 i2)
  let i3 ← lift (UScalar.cast .U64 field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← lift (Std.U64.wrapping_shr x1 31#u32)
  let x2 ← lift (Std.U64.wrapping_add i4 i5)
  let i6 ← lift (UScalar.cast .U32 x2)
  field.ct.subtract_p i6

def field.ct.add (a : Std.U32) (b : Std.U32) : Result Std.U32 := do
  let i ← lift (core.num.U32.wrapping_add a b)
  field.ct.subtract_p i

def field.ct.sub (a : Std.U32) (b : Std.U32) : Result Std.U32 := do
  let i ← lift (core.num.U32.wrapping_add a field.P)
  let i1 ← lift (core.num.U32.wrapping_sub i b)
  field.ct.subtract_p i1

def field.ct.neg (a : Std.U32) : Result Std.U32 := do
  let i ← lift (UScalar.cast_fromBool .U32 (a != 0#u32))
  let mask ← lift (core.num.U32.wrapping_sub 0#u32 i)
  let i1 ← lift (core.num.U32.wrapping_sub field.P a)
  ok (i1 &&& mask)

def field.ct.is_zero (a : Std.U32) : Result Bool := do
  ok (a = 0#u32)

def field.M31.Insts.CoreCmpPartialEqM31.eq
  (self : field.M31) (other : field.M31) :
  Result Bool
  := do
  ok (self = other)

def field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  field.ct.reduce64 x

def field.M31.mul
  (self : field.M31) (rhs : field.M31) :
  Result field.M31
  := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← lift (Std.U64.wrapping_mul i i1)
  let i3 ← field.reduce_u64 i2
  ok i3

def field.square_n_loop.body
  (iter : core.ops.range.Range Std.Usize) (value : field.M31) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    field.M31) field.M31)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done value)
  | some _ =>
    let value1 ← field.M31.mul value value
    ok (cont (iter1, value1))

def field.square_n_loop
  (iter : core.ops.range.Range Std.Usize) (value : field.M31) :
  Result field.M31
  := do
  loop
    (fun (iter1, value1) => field.square_n_loop.body iter1 value1)
    (iter, value)

def field.square_n
  (value : field.M31) (count : Std.Usize) :
  Result field.M31
  := do
  field.square_n_loop { start := 0#usize, «end» := count } value

def field.M31.reduce_u64
  (value : Std.U64) : Result field.M31 := do
  let i ← field.reduce_u64 value
  ok i

def field.M31.add
  (self : field.M31) (rhs : field.M31) :
  Result field.M31
  := do
  let i ← field.ct.add self rhs
  ok i

def field.M31.double
  (self : field.M31) : Result field.M31 := do
  field.M31.add self self

def field.M31.inv
  (self : field.M31) : Result field.M31 := do
  massert (self != 0#u32)
  let m ← field.M31.mul self self
  let t2 ← field.M31.mul m self
  let m1 ← field.square_n t2 2#usize
  let t4 ← field.M31.mul m1 t2
  let m2 ← field.square_n t4 4#usize
  let t8 ← field.M31.mul m2 t4
  let m3 ← field.square_n t8 8#usize
  let t16 ← field.M31.mul m3 t8
  let m4 ← field.square_n t16 8#usize
  let t24 ← field.M31.mul m4 t8
  let m5 ← field.square_n t24 4#usize
  let t28 ← field.M31.mul m5 t4
  let m6 ← field.M31.mul t28 t28
  let t29 ← field.M31.mul m6 self
  let t30 ← field.M31.mul t29 t29
  let m7 ← field.M31.mul t30 t30
  field.M31.mul m7 self

def field.M31.sub
  (self : field.M31) (rhs : field.M31) :
  Result field.M31
  := do
  let i ← field.ct.sub self rhs
  ok i

def field.M31.neg
  (self : field.M31) : Result field.M31 := do
  let i ← field.ct.neg self
  ok i

def field.M31.is_zero
  (self : field.M31) : Result Bool := do
  field.ct.is_zero self
#print axioms field.P
#print axioms field.ct.subtract_p
#print axioms field.ct.reduce64
#print axioms field.ct.add
#print axioms field.ct.sub
#print axioms field.ct.neg
#print axioms field.ct.is_zero
#print axioms field.M31.Insts.CoreCmpPartialEqM31.eq
#print axioms field.reduce_u64
#print axioms field.M31.mul
#print axioms field.square_n_loop.body
#print axioms field.square_n_loop
#print axioms field.square_n
#print axioms field.M31.reduce_u64
#print axioms field.M31.add
#print axioms field.M31.double
#print axioms field.M31.inv
#print axioms field.M31.sub
#print axioms field.M31.neg
#print axioms field.M31.is_zero
end R1Z.PV_RunJoin_CircleRawScalar52
