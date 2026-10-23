import Aeneas
import AspisR1ActualSemanticRoundCutV1.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

noncomputable section

namespace AspisR1ActualSemanticRoundCutV1

/-- [aspis_core::field::P] source: crates/aspis-core/src/field.rs:19:0-19:16.
Exact value from the pinned Rust source. -/
@[irreducible] def aspis_core.field.P : Result Std.U32 := .ok 2147483647#u32

/-- [aspis_core::field::{aspis_core::field::CM31}::new]
Source: crates/aspis-core/src/field.rs:271:4-271:38.
Exact constructor body: `CM31 { a, b }`. -/
def aspis_core.field.CM31.new
  (a : aspis_core.field.M31) (b : aspis_core.field.M31) : Result aspis_core.field.CM31 := do
  ok { a, b }

/-- [aspis_r1_cost_probe::sampler::qm31_div_pass]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/sampler.rs', lines 11:4-16:5 -/
@[rust_loop_body]
def sampler.qm31_div_pass_loop.body
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
    let i3 ← aspis_core.field.P
    let i4 ← lift (core.convert.num.FromU64U32.from i3)
    let i5 ← dividend / i4
    let i6 ← lift (UScalar.cast .U32 i5)
    let a ← Array.update rank j1 i6
    let i7 ← lift (core.convert.num.FromU64U32.from i3)
    let remainder1 ← dividend % i7
    ok (cont (a, remainder1, j1))
  else ok (done (rank, remainder))

/-- [aspis_r1_cost_probe::sampler::qm31_div_pass]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/sampler.rs', lines 11:4-16:5 -/
@[rust_loop]
def sampler.qm31_div_pass_loop
  (rank : Array Std.U32 8#usize) (remainder : Std.U64) (j : Std.Usize) :
  Result ((Array Std.U32 8#usize) × Std.U64)
  := do
  loop
    (fun (rank1, remainder1, j1) => sampler.qm31_div_pass_loop.body rank1
      remainder1 j1)
    (rank, remainder, j)

/-- [aspis_r1_cost_probe::sampler::qm31_div_pass]:
    Source: 'crates/aspis-r1-cost-probe/src/sampler.rs', lines 8:0-18:1 -/
def sampler.qm31_div_pass
  (rank : Array Std.U32 8#usize) :
  Result ((Array Std.U32 8#usize) × Std.U32)
  := do
  let (rank1, remainder) ← sampler.qm31_div_pass_loop rank 0#u64 8#usize
  let i ← lift (UScalar.cast .U32 remainder)
  ok (rank1, i)

/-- [aspis_r1_cost_probe::sampler::qm31_digits]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/sampler.rs', lines 24:4-33:5 -/
@[rust_loop_body]
def sampler.qm31_digits_loop0.body
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
    let a ← Array.update rank i i8
    let i9 ← lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (a, i9))
  else ok (done rank)

/-- [aspis_r1_cost_probe::sampler::qm31_digits]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/sampler.rs', lines 24:4-33:5 -/
@[rust_loop]
def sampler.qm31_digits_loop0
  (block : Array Std.U8 32#usize) (rank : Array Std.U32 8#usize)
  (i : Std.Usize) :
  Result (Array Std.U32 8#usize)
  := do
  loop
    (fun (rank1, i1) => sampler.qm31_digits_loop0.body block rank1 i1)
    (rank, i)

/-- [aspis_r1_cost_probe::sampler::qm31_digits]: loop body 1:
    Source: 'crates/aspis-r1-cost-probe/src/sampler.rs', lines 36:4-41:5 -/
@[rust_loop_body]
def sampler.qm31_digits_loop1.body
  (rank : Array Std.U32 8#usize) (digits : Array Std.U32 4#usize)
  (i : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 8#usize) × (Array Std.U32 4#usize) ×
    Std.Usize) (Array Std.U32 4#usize))
  := do
  if i < 4#usize
  then
    let (quotient, digit) ← sampler.qm31_div_pass rank
    let a ← Array.update digits i digit
    let i1 ← lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (quotient, a, i1))
  else ok (done digits)

/-- [aspis_r1_cost_probe::sampler::qm31_digits]: loop 1:
    Source: 'crates/aspis-r1-cost-probe/src/sampler.rs', lines 36:4-41:5 -/
@[rust_loop]
def sampler.qm31_digits_loop1
  (rank : Array Std.U32 8#usize) (digits : Array Std.U32 4#usize)
  (i : Std.Usize) :
  Result (Array Std.U32 4#usize)
  := do
  loop
    (fun (rank1, digits1, i1) => sampler.qm31_digits_loop1.body rank1 digits1
      i1)
    (rank, digits, i)

/-- [aspis_r1_cost_probe::sampler::qm31_digits]:
    Source: 'crates/aspis-r1-cost-probe/src/sampler.rs', lines 21:0-43:1 -/
def sampler.qm31_digits
  (block : Array Std.U8 32#usize) : Result (Array Std.U32 4#usize) := do
  let rank := Array.repeat 8#usize 0#u32
  let rank1 ← sampler.qm31_digits_loop0 block rank 0#usize
  let digits := Array.repeat 4#usize 0#u32
  sampler.qm31_digits_loop1 rank1 digits 0#usize

/-- [aspis_r1_cost_probe::sampler::qm31_sample]:
    Source: 'crates/aspis-r1-cost-probe/src/sampler.rs', lines 45:0-51:1
    Visibility: public -/
def sampler.qm31_sample
  (block : Array Std.U8 32#usize) : Result aspis_core.field.QM31 := do
  let digits ← sampler.qm31_digits block
  let i ← Array.index_usize digits 0#usize
  let i1 ← Array.index_usize digits 1#usize
  let c ← aspis_core.field.CM31.new i i1
  let i2 ← Array.index_usize digits 2#usize
  let i3 ← Array.index_usize digits 3#usize
  let c1 ← aspis_core.field.CM31.new i2 i3
  ok { c0 := c, c1 }


/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::SemanticTranscript<H>}::sample_block_validated]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 194:4-208:5 -/
def r1_wire.SemanticTranscript.sample_block_validated
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : r1_wire.SemanticTranscript H) (row : Std.U8) (framed : Slice Std.U8)
  :
  Result ((core.result.Result (Array Std.U8 32#usize) r1_wire.Error) ×
    (r1_wire.SemanticTranscript H))
  := do
  if row != self.next_row
  then
    ok (core.result.Result.Err (r1_wire.Error.RowOrder self.next_row row),
      self)
  else
    let s ← lift (Array.to_slice self.state)
    let i ← lift (Std.U8.wrapping_add 160#u8 row)
    let s1 ← lift (Array.to_slice (Array.make 2#usize [ 0#u8, i ]))
    let s2 ← lift (Array.to_slice (Array.make 3#usize [ s, s1, framed ]))
    let absorbed ← aspis_coredigestDigest32Inst.digest self.hash s2
    let s3 ← lift (Array.to_slice absorbed)
    let s4 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
    let s5 ← lift (Array.to_slice (Array.make 2#usize [ s3, s4 ]))
    let block ← aspis_coredigestDigest32Inst.digest self.hash s5
    let s6 ← lift (Array.to_slice absorbed)
    let s7 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
    let s8 ← lift (Array.to_slice (Array.make 2#usize [ s6, s7 ]))
    let a ← aspis_coredigestDigest32Inst.digest self.hash s8
    let i1 ← lift (Std.U8.wrapping_add self.next_row 1#u8)
    ok (core.result.Result.Ok block, { self with state := a, next_row := i1 })

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::ValidatedRecord<'a>}::framed]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 127:4-129:5 -/
def r1_wire.ValidatedRecord.impl.framed
  (self : r1_wire.ValidatedRecord) : Result (Slice Std.U8) := do
  ok self.framed

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::ValidatedRecord<'a>}::row]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 123:4-125:5 -/
def r1_wire.ValidatedRecord.impl.row
  (self : r1_wire.ValidatedRecord) : Result Std.U8 := do
  ok self.row

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::SemanticTranscript<H>}::semantic_validated]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 220:4-231:5 -/
def r1_wire.SemanticTranscript.semantic_validated
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) :
  Result ((core.result.Result aspis_core.field.QM31 r1_wire.Error) ×
    (r1_wire.SemanticTranscript H))
  := do
  let row ← r1_wire.ValidatedRecord.impl.row record1
  if row > 24#u8
  then ok (core.result.Result.Err r1_wire.Error.InvalidRow, self)
  else
    let s ← r1_wire.ValidatedRecord.impl.framed record1
    let (r, self1) ←
      r1_wire.SemanticTranscript.sample_block_validated
        aspis_coredigestDigest32Inst self row s
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let q ← sampler.qm31_sample val
      ok (core.result.Result.Ok q, self1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.QM31 (core.convert.FromSame r1_wire.Error) residual
      ok (r1, self1)

end AspisR1ActualSemanticRoundCutV1
