-- PCWR_ item 4 (r1): AspisR1Qm31SamplerIndex.Funs, fresh = gate with NO external shim.
-- Fresh text: PCWR_E002 emission (original Aeneas 959659a6, overflow checks ON, frozen 4bb3b3f, cargo --jobs 4, CARGO_BUILD_JOBS=4, rustc -Zthreads 1,
-- identity by class receipt PCWE_E003), the PCQK_E015 root set with `--include aspis_core::field::P --include aspis_core::field::_::new`, so that
-- aspis_core::field::P and aspis_core::field::CM31::new are emitted frozen definitions (a U32 constant and `ok { a, b }`), not externals.
-- The blocks below are copied verbatim from PCWR_E002_emitted/raw/PCWR_qs/Funs.lean (namespace changed; maxHeartbeats header dropped, default 200000 used).
-- The only binding left is the type alias of the three aspis_core field structures to the gate types (Types isomorphism is proved separately in PCQK/PCWM).
import Aeneas
import AspisR1Qm31SamplerIndex.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1Qm31SamplerIndex
namespace PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1
abbrev aspis_core.field.CM31 := AspisR1Qm31SamplerIndex.field.CM31
abbrev aspis_core.field.M31 := AspisR1Qm31SamplerIndex.field.M31
abbrev aspis_core.field.QM31 := AspisR1Qm31SamplerIndex.field.QM31

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:16
    Name pattern: [aspis_core::field::P]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_core::field::P"]
def aspis_core.field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::{aspis_core::field::CM31}::new]:
    Source: 'crates/aspis-core/src/field.rs', lines 271:4-271:38
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::new]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::new"]
def aspis_core.field.CM31.new
  (a : aspis_core.field.M31) (b : aspis_core.field.M31) :
  Result aspis_core.field.CM31
  := do
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
    let j1 ← j - 1#usize
    let i ← remainder <<< 32#i32
    let i1 ← Array.index_usize rank j1
    let i2 ← lift (core.convert.num.FromU64U32.from i1)
    let dividend ← lift (i ||| i2)
    let i3 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let i4 ← dividend / i3
    let i5 ← lift (UScalar.cast .U32 i4)
    let a ← Array.update rank j1 i5
    let i6 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let remainder1 ← dividend % i6
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
    let start ← 4#usize * i
    let i1 ← Array.index_usize block start
    let i2 ← start + 1#usize
    let i3 ← Array.index_usize block i2
    let i4 ← start + 2#usize
    let i5 ← Array.index_usize block i4
    let i6 ← start + 3#usize
    let i7 ← Array.index_usize block i6
    let i8 ←
      lift (core.num.U32.from_le_bytes (Array.make 4#usize [ i1, i3, i5, i7 ]))
    let a ← Array.update rank i i8
    let i9 ← i + 1#usize
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
    let i1 ← i + 1#usize
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

end PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1
end AspisR1Qm31SamplerIndex

namespace PRVEq.AspisR1Qm31SamplerIndex.Funs_r1
open AspisR1Qm31SamplerIndex

set_option maxHeartbeats 200000 in
theorem field_P : @AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.aspis_core.field.P = @AspisR1Qm31SamplerIndex.field.P := by
  first | rfl | (delta AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.aspis_core.field.P AspisR1Qm31SamplerIndex.field.P; try rfl; done)
#print axioms field_P

set_option maxHeartbeats 200000 in
theorem field_CM31_new : @AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.aspis_core.field.CM31.new = @AspisR1Qm31SamplerIndex.field.CM31.new := by
  first | rfl | (delta AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.aspis_core.field.CM31.new AspisR1Qm31SamplerIndex.field.CM31.new; try rfl; done)
#print axioms field_CM31_new

set_option maxHeartbeats 200000 in
theorem sampler_qm31_div_pass_loop_body : @AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_div_pass_loop.body = @AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop.body := by
  first | rfl | (delta AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_div_pass_loop.body AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop.body; try simp only [field_P]; try rfl; done)
#print axioms sampler_qm31_div_pass_loop_body

set_option maxHeartbeats 200000 in
theorem sampler_qm31_div_pass_loop : @AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_div_pass_loop = @AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop := by
  first | rfl | (delta AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_div_pass_loop AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop; (try rw [sampler_qm31_div_pass_loop_body]); try simp only [field_P]; try rfl; done)
#print axioms sampler_qm31_div_pass_loop

set_option maxHeartbeats 200000 in
theorem sampler_qm31_div_pass : @AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_div_pass = @AspisR1Qm31SamplerIndex.sampler.qm31_div_pass := by
  first | rfl | (delta AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_div_pass AspisR1Qm31SamplerIndex.sampler.qm31_div_pass; (try rw [sampler_qm31_div_pass_loop]); try simp only [field_P]; try rfl; done)
#print axioms sampler_qm31_div_pass

set_option maxHeartbeats 200000 in
theorem sampler_qm31_digits_loop0_body : @AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_digits_loop0.body = @AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop0.body := by
  first | rfl | (delta AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_digits_loop0.body AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop0.body; try simp only [field_P]; try rfl; done)
#print axioms sampler_qm31_digits_loop0_body

set_option maxHeartbeats 200000 in
theorem sampler_qm31_digits_loop0 : @AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_digits_loop0 = @AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop0 := by
  first | rfl | (delta AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_digits_loop0 AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop0; (try rw [sampler_qm31_digits_loop0_body]); try simp only [field_P]; try rfl; done)
#print axioms sampler_qm31_digits_loop0

set_option maxHeartbeats 200000 in
theorem sampler_qm31_digits_loop1_body : @AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_digits_loop1.body = @AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop1.body := by
  first | rfl | (delta AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_digits_loop1.body AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop1.body; (try rw [sampler_qm31_div_pass]); try simp only [field_P]; try rfl; done)
#print axioms sampler_qm31_digits_loop1_body

set_option maxHeartbeats 200000 in
theorem sampler_qm31_digits_loop1 : @AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_digits_loop1 = @AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop1 := by
  first | rfl | (delta AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_digits_loop1 AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop1; (try rw [sampler_qm31_digits_loop1_body]); try simp only [field_P]; try rfl; done)
#print axioms sampler_qm31_digits_loop1

set_option maxHeartbeats 200000 in
theorem sampler_qm31_digits : @AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_digits = @AspisR1Qm31SamplerIndex.sampler.qm31_digits := by
  first | rfl | (delta AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_digits AspisR1Qm31SamplerIndex.sampler.qm31_digits; (try rw [sampler_qm31_digits_loop0]); (try rw [sampler_qm31_digits_loop1]); try simp only [field_P]; try rfl; done)
#print axioms sampler_qm31_digits

set_option maxHeartbeats 200000 in
theorem sampler_qm31_sample : @AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_sample = @AspisR1Qm31SamplerIndex.sampler.qm31_sample := by
  first | rfl | (delta AspisR1Qm31SamplerIndex.PRVFresh_AspisR1Qm31SamplerIndex_Funs_r1.sampler.qm31_sample AspisR1Qm31SamplerIndex.sampler.qm31_sample; (try rw [sampler_qm31_digits]); (try rw [field_CM31_new]); try simp only [field_P]; try rfl; done)
#print axioms sampler_qm31_sample

end PRVEq.AspisR1Qm31SamplerIndex.Funs_r1
