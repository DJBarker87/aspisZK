import R1Z.PV_RunJoin_CircleRawTower52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleRawSampler52
def shipped_sampler.qm31_div_pass_loop.body
  (rank : Array Std.U32 8#usize) (remainder : Std.U64) (j : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 8#usize) × Std.U64 × Std.Usize) ((Array
    Std.U32 8#usize) × Std.U64))
  := do
  if j > 0#usize
  then
    let j1 ← lift (Std.Usize.wrapping_sub j 1#usize)
    let i ← lift (Std.U64.wrapping_shl remainder 32#u32)
    let i1 ← Array.index_usize rank j1
    let i2 ← lift (core.convert.num.FromU64U32.from i1)
    let dividend ← lift (i ||| i2)
    let i3 ← lift (core.convert.num.FromU64U32.from PV_RunJoin_CircleRawTower52.field.P)
    let i4 ← dividend / i3
    let i5 ← lift (UScalar.cast .U32 i4)
    let rank1 ← Array.update rank j1 i5
    let i6 ← lift (core.convert.num.FromU64U32.from PV_RunJoin_CircleRawTower52.field.P)
    let remainder1 ← dividend % i6
    ok (cont (rank1, remainder1, j1))
  else ok (done (rank, remainder))

def shipped_sampler.qm31_div_pass_loop
  (rank : Array Std.U32 8#usize) (remainder : Std.U64) (j : Std.Usize) :
  Result ((Array Std.U32 8#usize) × Std.U64)
  := do
  loop
    (fun (rank1, remainder1, j1) => shipped_sampler.qm31_div_pass_loop.body
      rank1 remainder1 j1)
    (rank, remainder, j)

def shipped_sampler.qm31_div_pass
  (rank : Array Std.U32 8#usize) :
  Result ((Array Std.U32 8#usize) × Std.U32)
  := do
  let (rank1, remainder) ←
    shipped_sampler.qm31_div_pass_loop rank 0#u64 8#usize
  let i ← lift (UScalar.cast .U32 remainder)
  ok (rank1, i)

def shipped_sampler.qm31_digits_loop0.body
  (block : Array Std.U8 32#usize) (rank : Array Std.U32 8#usize)
  (i : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 8#usize) × Std.Usize) (Array Std.U32
    8#usize))
  := do
  if i < 8#usize
  then
    let start ← lift (Std.Usize.wrapping_mul 4#usize i)
    let i1 ← Array.index_usize block start
    let i2 ← lift (Std.Usize.wrapping_add start 1#usize)
    let i3 ← Array.index_usize block i2
    let i4 ← lift (Std.Usize.wrapping_add start 2#usize)
    let i5 ← Array.index_usize block i4
    let i6 ← lift (Std.Usize.wrapping_add start 3#usize)
    let i7 ← Array.index_usize block i6
    let i8 ←
      lift (core.num.U32.from_le_bytes (Array.make 4#usize [ i1, i3, i5, i7 ]))
    let rank1 ← Array.update rank i i8
    let i9 ← lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (rank1, i9))
  else ok (done rank)

def shipped_sampler.qm31_digits_loop0
  (block : Array Std.U8 32#usize) (rank : Array Std.U32 8#usize)
  (i : Std.Usize) :
  Result (Array Std.U32 8#usize)
  := do
  loop
    (fun (rank1, i1) => shipped_sampler.qm31_digits_loop0.body block rank1 i1)
    (rank, i)

def shipped_sampler.qm31_digits_loop1.body
  (rank : Array Std.U32 8#usize) (digits : Array Std.U32 4#usize)
  (i : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 8#usize) × (Array Std.U32 4#usize) ×
    Std.Usize) (Array Std.U32 4#usize))
  := do
  if i < 4#usize
  then
    let (quotient, digit) ← shipped_sampler.qm31_div_pass rank
    let digits1 ← Array.update digits i digit
    let i1 ← lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (quotient, digits1, i1))
  else ok (done digits)

def shipped_sampler.qm31_digits_loop1
  (rank : Array Std.U32 8#usize) (digits : Array Std.U32 4#usize)
  (i : Std.Usize) :
  Result (Array Std.U32 4#usize)
  := do
  loop
    (fun (rank1, digits1, i1) => shipped_sampler.qm31_digits_loop1.body rank1
      digits1 i1)
    (rank, digits, i)

def shipped_sampler.qm31_digits
  (block : Array Std.U8 32#usize) : Result (Array Std.U32 4#usize) := do
  let rank := Array.repeat 8#usize 0#u32
  let rank1 ← shipped_sampler.qm31_digits_loop0 block rank 0#usize
  let digits := Array.repeat 4#usize 0#u32
  shipped_sampler.qm31_digits_loop1 rank1 digits 0#usize

def shipped_sampler.qm31_sample
  (block : Array Std.U8 32#usize) : Result PV_RunJoin_CircleRawTower52.field.QM31 := do
  let digits ← shipped_sampler.qm31_digits block
  let i ← Array.index_usize digits 0#usize
  let i1 ← Array.index_usize digits 1#usize
  let c ← PV_RunJoin_CircleRawTower52.field.CM31.new i i1
  let i2 ← Array.index_usize digits 2#usize
  let i3 ← Array.index_usize digits 3#usize
  let c1 ← PV_RunJoin_CircleRawTower52.field.CM31.new i2 i3
  ok { fst := c, snd := c1 }
#print axioms shipped_sampler.qm31_div_pass_loop.body
#print axioms shipped_sampler.qm31_div_pass_loop
#print axioms shipped_sampler.qm31_div_pass
#print axioms shipped_sampler.qm31_digits_loop0.body
#print axioms shipped_sampler.qm31_digits_loop0
#print axioms shipped_sampler.qm31_digits_loop1.body
#print axioms shipped_sampler.qm31_digits_loop1
#print axioms shipped_sampler.qm31_digits
#print axioms shipped_sampler.qm31_sample
end R1Z.PV_RunJoin_CircleRawSampler52
