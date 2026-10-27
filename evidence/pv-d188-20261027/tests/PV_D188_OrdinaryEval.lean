import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_D188_Ordinary
@[global_simps, irreducible, rust_const "aspis_core::field::P"]
def aspis_core.field.P : Std.U32 := 2147483647#u32

/-- [prover_rw_success_p8::sampler_owned::qm31_div_pass]: loop body 0:
    Source: 'sampler_owned.rs', lines 5:1-10:2
    Visibility: public -/
@[rust_loop_body]
def sampler_owned.qm31_div_pass_loop.body
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
    let i3 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let i4 ← dividend / i3
    let i5 ← lift (UScalar.cast .U32 i4)
    let rank1 ← Array.update rank j1 i5
    let i6 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let remainder1 ← dividend % i6
    ok (cont (rank1, remainder1, j1))
  else ok (done (rank, remainder))

/-- [prover_rw_success_p8::sampler_owned::qm31_div_pass]: loop 0:
    Source: 'sampler_owned.rs', lines 5:1-10:2
    Visibility: public -/
@[rust_loop]
def sampler_owned.qm31_div_pass_loop
  (rank : Array Std.U32 8#usize) (remainder : Std.U64) (j : Std.Usize) :
  Result ((Array Std.U32 8#usize) × Std.U64)
  := do
  loop
    (fun (rank1, remainder1, j1) => sampler_owned.qm31_div_pass_loop.body rank1
      remainder1 j1)
    (rank, remainder, j)

/-- [prover_rw_success_p8::sampler_owned::qm31_div_pass]:
    Source: 'sampler_owned.rs', lines 3:0-12:1
    Visibility: public -/
def sampler_owned.qm31_div_pass
  (rank : Array Std.U32 8#usize) :
  Result ((Array Std.U32 8#usize) × Std.U32)
  := do
  let (rank1, remainder) ←
    sampler_owned.qm31_div_pass_loop rank 0#u64 8#usize
  let i ← lift (UScalar.cast .U32 remainder)
  ok (rank1, i)

/-- [prover_rw_success_p8::sampler_owned::low_base_p_digits]: loop body 0:
    Source: 'sampler_owned.rs', lines 15:1-19:2
    Visibility: public -/
@[rust_loop_body]
def sampler_owned.low_base_p_digits_loop0.body
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

/-- [prover_rw_success_p8::sampler_owned::low_base_p_digits]: loop 0:
    Source: 'sampler_owned.rs', lines 15:1-19:2
    Visibility: public -/
@[rust_loop]
def sampler_owned.low_base_p_digits_loop0
  (block : Array Std.U8 32#usize) (rank : Array Std.U32 8#usize)
  (i : Std.Usize) :
  Result (Array Std.U32 8#usize)
  := do
  loop
    (fun (rank1, i1) => sampler_owned.low_base_p_digits_loop0.body block rank1
      i1)
    (rank, i)

/-- [prover_rw_success_p8::sampler_owned::low_base_p_digits]: loop body 1:
    Source: 'sampler_owned.rs', lines 21:1-24:2
    Visibility: public -/
@[rust_loop_body]
def sampler_owned.low_base_p_digits_loop1.body
  (rank : Array Std.U32 8#usize) (digits : Array Std.U32 8#usize)
  (i : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 8#usize) × (Array Std.U32 8#usize) ×
    Std.Usize) ((Array Std.U32 8#usize) × (Array Std.U32 8#usize)))
  := do
  if i < 8#usize
  then
    let (quotient, digit) ← sampler_owned.qm31_div_pass rank
    let digits1 ← Array.update digits i digit
    let i1 ← lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (quotient, digits1, i1))
  else ok (done (rank, digits))

/-- [prover_rw_success_p8::sampler_owned::low_base_p_digits]: loop 1:
    Source: 'sampler_owned.rs', lines 21:1-24:2
    Visibility: public -/
@[rust_loop]
def sampler_owned.low_base_p_digits_loop1
  (rank : Array Std.U32 8#usize) (digits : Array Std.U32 8#usize)
  (i : Std.Usize) :
  Result ((Array Std.U32 8#usize) × (Array Std.U32 8#usize))
  := do
  loop
    (fun (rank1, digits1, i1) => sampler_owned.low_base_p_digits_loop1.body
      rank1 digits1 i1)
    (rank, digits, i)

/-- [prover_rw_success_p8::sampler_owned::low_base_p_digits]:
    Source: 'sampler_owned.rs', lines 13:0-26:1
    Visibility: public -/
def sampler_owned.low_base_p_digits
  (block : Array Std.U8 32#usize) :
  Result ((Array Std.U32 8#usize) × Std.U32)
  := do
  let rank := Array.repeat 8#usize 0#u32
  let rank1 ← sampler_owned.low_base_p_digits_loop0 block rank 0#usize
  let digits := Array.repeat 8#usize 0#u32
  let (rank2, digits1) ←
    sampler_owned.low_base_p_digits_loop1 rank1 digits 0#usize
  let i ← Array.index_usize rank2 0#usize
  ok (digits1, i)


-- Tests of the retained indexed-copy emission, not a new source law.
#eval ([0#u32,2147483647#u32,2147483648#u32].map fun n =>
  (do let b ← lift (Array.to_slice (Array.repeat 32#usize 0#u8))
      let a ← lift (Array.to_slice (core.num.U32.to_le_bytes n))
      let b ← Slice.update b 0#usize (a.val[0]!)
      let b ← Slice.update b 1#usize (a.val[1]!)
      let b ← Slice.update b 2#usize (a.val[2]!)
      let b ← Slice.update b 3#usize (a.val[3]!)
      let (d,q) ← sampler_owned.low_base_p_digits (Array.from_slice (Array.repeat 32#usize 0#u8) b)
      ok (d.val.map (fun x => x.val),q.val) : Result (List Nat × Nat)))
#eval (do let (d,q) ← sampler_owned.low_base_p_digits (Array.repeat 32#usize 255#u8)
          ok (d.val.map (fun x => x.val),q.val) : Result (List Nat × Nat))

end PV_D188_Ordinary
