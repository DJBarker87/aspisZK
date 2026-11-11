-- PIN2 NEW GATE for the verifier prefix (VerifyPrefix.verify = r1_semantic::verify_observed under the recorded fe80/RPz7 substitution)
-- at source c7593d23fdc56fcee9a9df1628d5f63b52ac7a95. Lead option A: twin PIN2 types, composed with the overlay PIN2_NEWGATE_r0/_r1_semantic.
-- Section 1: emission PW8_E004, Charon 454586e9 + Aeneas 0d21a9ec, overflow-checks ON, features private-leaf-salts,optimized-terminal,program-build,
--   cargo --jobs 4 / CARGO_BUILD_JOBS=4, rustc -Zthreads=1, identity by class receipt PCWE_E003; raw sha256 Types.lean 61f0d00deae155032cb4ca3305331c55a6bf8ed0cc6c526525941aca0a2754b0 Funs.lean 409ada7c87e0b7ebc212a32f437eacf729c273b10eb2d808182ea710ef3e9a81.
-- Section 2: PrefixAdapter = frozen ExtractedPrefixParseCore (sha256 2363d2b0e1d059caaf61594416ce21e8b3b3fea9da39eace4f93344a61eaa343), namespace changed only.
-- Section 3: VerifyPrefix from PW8_SUBSTITUTION.json (input PW8_E003 Funs.lean sha256 92d5f52e8f620cfa31202c6c4e6adc33e580f371bf64b7d8f4f676d8676b0376, Charon daad69be + Aeneas b59d5188-lean432-extended; output sha256 e36816857b36099e83cd660918f975a0f35cabefa944b74d8bea078672e3955f).
-- Built by PW8_mk_newgate.py; declarations of the overlay NEWGATE files are imported, not repeated. No placeholder proof, no axiom.
import Aeneas
import PIN2_NEWGATE_r1_semantic
import AspisR1PrefixAggregateParser.Funs
import RPz7_PhaseIso
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxRecDepth 2048

/- Aeneas-generated default heartbeat budget for the emitted definitions (same as PIN2_NEWGATE_r0/_r1_semantic). -/
set_option maxHeartbeats 1000000

namespace AspisR1PublicPreparationPIN2

/-- [aspis_core::field::CM31]
    Source: 'crates/aspis-core/src/field.rs', lines 255:0-255:15
    Name pattern: [aspis_core::field::CM31]
    Visibility: public -/
@[rust_type "aspis_core::field::CM31"]
structure aspis_core.field.CM31 where
  a : aspis_core.field.M31
  b : aspis_core.field.M31

/-- [aspis_core::field::QM31]
    Source: 'crates/aspis-core/src/field.rs', lines 432:0-432:15
    Name pattern: [aspis_core::field::QM31]
    Visibility: public -/
@[rust_type "aspis_core::field::QM31"]
structure aspis_core.field.QM31 where
  c0 : aspis_core.field.CM31
  c1 : aspis_core.field.CM31

/-- [aspis_core::circle::SecureCirclePoint]
    Source: 'crates/aspis-core/src/circle.rs', lines 11:0-11:28
    Name pattern: [aspis_core::circle::SecureCirclePoint]
    Visibility: public -/
@[rust_type "aspis_core::circle::SecureCirclePoint"]
structure aspis_core.circle.SecureCirclePoint where
  x : aspis_core.field.QM31
  y : aspis_core.field.QM31

/-- [aspis_core::state_only_prefix::r0::Challenges]
    Source: 'crates/aspis-core/src/state_only_prefix.rs', lines 1840:4-1840:25
    Name pattern: [aspis_core::state_only_prefix::r0::Challenges]
    Visibility: public -/
@[rust_type "aspis_core::state_only_prefix::r0::Challenges"]
structure aspis_core.state_only_prefix.r0.Challenges where
  lambda : aspis_core.field.QM31
  chi : aspis_core.field.QM31
  theta : aspis_core.field.QM31
  zc : Array aspis_core.field.QM31 10#usize
  mu : aspis_core.field.QM31
  eta : aspis_core.field.QM31

/-- [aspis_r1_cost_probe::r1_semantic::Verified]
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 7:0-23:1
    Visibility: public -/
structure r1_semantic.Verified (H : Type _) where
  roots : Array (Array Std.U8 32#usize) 2#usize
  challenges : aspis_core.state_only_prefix.r0.Challenges
  alpha : Array aspis_core.field.QM31 10#usize
  claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize
  extra : Array aspis_core.field.QM31 29#usize
  before_z1 : Array aspis_core.field.QM31 29#usize
  state_before_z0 : Array Std.U8 32#usize
  z : Array aspis_core.circle.SecureCirclePoint 2#usize
  transcript : r1_wire.SemanticTranscript H

/-- [aspis_r1_cost_probe::r1_wire::ValidatedRecord]
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 117:0-120:1 -/
structure r1_wire.ValidatedRecord where
  row : Std.U8
  framed : Slice Std.U8

/-- [aspis_r1_cost_probe::r1_wire::Prefix]
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 273:0-276:1
    Visibility: public -/
structure r1_wire.Prefix where
  c1_root : Array Std.U8 32#usize
  records : Array (Slice Std.U8) 27#usize

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

/-- [aspis_core::field::{aspis_core::field::QM31}::ZERO]
    Source: 'crates/aspis-core/src/field.rs', lines 869:4-869:24
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::ZERO]
    Visibility: public -/
@[global_simps, irreducible]
def aspis_core.field.QM31.ZERO : aspis_core.field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::ValidatedRecord<'a>}::row]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 123:4-125:5 -/
def r1_wire.ValidatedRecord.impl.row
  (self : r1_wire.ValidatedRecord) : Result Std.U8 := do
  ok self.row

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::ValidatedRecord<'a>}::framed]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 127:4-129:5 -/
def r1_wire.ValidatedRecord.impl.framed
  (self : r1_wire.ValidatedRecord) : Result (Slice Std.U8) := do
  ok self.framed

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::SemanticTranscript<H>}::sample_block_validated]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 194:4-208:5 -/
def r1_wire.SemanticTranscript.sample_block_validated
  {H : Type _} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
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
    let i ← 160#u8 + row
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
    let i1 ← self.next_row + 1#u8
    ok (core.result.Result.Ok block, { self with state := a, next_row := i1 })

/-- [aspis_r1_cost_probe::sampler::qm31_div_pass]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/sampler.rs', lines 11:4-16:5 -/
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

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::SemanticTranscript<H>}::semantic_validated]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 220:4-231:5 -/
def r1_wire.SemanticTranscript.semantic_validated
  {H : Type _} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord) :
  Result ((core.result.Result aspis_core.field.QM31 r1_wire.Error) ×
    (r1_wire.SemanticTranscript H))
  := do
  let row ← r1_wire.ValidatedRecord.impl.row record
  if row > 24#u8
  then ok (core.result.Result.Err r1_wire.Error.InvalidRow, self)
  else
    let s ← r1_wire.ValidatedRecord.impl.framed record
    let (r, self1) ←
      r1_wire.SemanticTranscript.sample_block_validated
        aspis_coredigestDigest32Inst self row s
    let cf ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let q ← sampler.qm31_sample val
      ok (core.result.Result.Ok q, self1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          aspis_core.field.QM31 (core.convert.FromSame r1_wire.Error) residual
      ok (r1, self1)

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::Prefix<'a>}::record]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 338:4-343:5
    Visibility: public -/
def r1_wire.Prefix.record
  (self : r1_wire.Prefix) (row : Std.U8) :
  Result (core.result.Result (Slice Std.U8) r1_wire.Error)
  := do
  if row >= 27#u8
  then ok (core.result.Result.Err r1_wire.Error.InvalidRow)
  else
    let i ← lift (UScalar.cast .Usize row)
    let s ← Array.index_usize self.records i
    ok (core.result.Result.Ok s)

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::Prefix<'a>}::validated_record]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 348:4-353:5 -/
def r1_wire.Prefix.validated_record
  (self : r1_wire.Prefix) (row : Std.U8) :
  Result (core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
  := do
  let r ← r1_wire.Prefix.record self row
  let cf ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok { row, framed := val })
  | core.ops.control_flow.ControlFlow.Break residual =>
    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      r1_wire.ValidatedRecord (core.convert.FromSame r1_wire.Error) residual

/-- [aspis_r1_cost_probe::r1_wire::begin]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 390:0-418:1
    Visibility: public -/
def r1_wire.begin
  {H : Type _} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  («prefix» : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
  Result ((core.result.Result aspis_core.state_only_prefix.r0.Challenges
    r1_wire.Error) × (r1_wire.SemanticTranscript H))
  := do
  let r ← r1_wire.Prefix.validated_record «prefix» 0#u8
  let cf ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    let (r1, transcript1) ←
      r1_wire.SemanticTranscript.semantic_validated
        aspis_coredigestDigest32Inst transcript vr
    let cf1 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r2 ← r1_wire.Prefix.validated_record «prefix» 1#u8
      let cf2 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue vr1 =>
        let (r3, transcript2) ←
          r1_wire.SemanticTranscript.semantic_validated
            aspis_coredigestDigest32Inst transcript1 vr1
        let cf3 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let r4 ← r1_wire.Prefix.validated_record «prefix» 2#u8
          let cf4 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue vr2 =>
            let (r5, transcript3) ←
              r1_wire.SemanticTranscript.semantic_validated
                aspis_coredigestDigest32Inst transcript2 vr2
            let cf5 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val2 =>
              let zc := Array.repeat 10#usize aspis_core.field.QM31.ZERO
              let r6 ← r1_wire.Prefix.validated_record «prefix» 3#u8
              let cf6 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue vr3 =>
                let (r7, transcript4) ←
                  r1_wire.SemanticTranscript.semantic_validated
                    aspis_coredigestDigest32Inst transcript3 vr3
                let cf7 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r7
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let (_, index_mut_back) ← Array.index_mut_usize zc 0#usize
                  let r8 ← r1_wire.Prefix.validated_record «prefix» 4#u8
                  let cf8 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue vr4 =>
                    let (r9, transcript5) ←
                      r1_wire.SemanticTranscript.semantic_validated
                        aspis_coredigestDigest32Inst transcript4 vr4
                    let cf9 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r9
                    match cf9 with
                    | core.ops.control_flow.ControlFlow.Continue val4 =>
                      let zc1 := index_mut_back val3
                      let (_, index_mut_back1) ←
                        Array.index_mut_usize zc1 1#usize
                      let r10 ←
                        r1_wire.Prefix.validated_record «prefix» 5#u8
                      let cf10 ←
                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r10
                      match cf10 with
                      | core.ops.control_flow.ControlFlow.Continue vr5 =>
                        let (r11, transcript6) ←
                          r1_wire.SemanticTranscript.semantic_validated
                            aspis_coredigestDigest32Inst transcript5 vr5
                        let cf11 ←
                          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r11
                        match cf11 with
                        | core.ops.control_flow.ControlFlow.Continue val5 =>
                          let zc2 := index_mut_back1 val4
                          let (_, index_mut_back2) ←
                            Array.index_mut_usize zc2 2#usize
                          let r12 ←
                            r1_wire.Prefix.validated_record «prefix» 6#u8
                          let cf12 ←
                            PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r12
                          match cf12 with
                          | core.ops.control_flow.ControlFlow.Continue vr6 =>
                            let (r13, transcript7) ←
                              r1_wire.SemanticTranscript.semantic_validated
                                aspis_coredigestDigest32Inst transcript6 vr6
                            let cf13 ←
                              PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r13
                            match cf13 with
                            | core.ops.control_flow.ControlFlow.Continue val6
                              =>
                              let zc3 := index_mut_back2 val5
                              let (_, index_mut_back3) ←
                                Array.index_mut_usize zc3 3#usize
                              let r14 ←
                                r1_wire.Prefix.validated_record «prefix» 7#u8
                              let cf14 ←
                                PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r14
                              match cf14 with
                              | core.ops.control_flow.ControlFlow.Continue vr7
                                =>
                                let (r15, transcript8) ←
                                  r1_wire.SemanticTranscript.semantic_validated
                                    aspis_coredigestDigest32Inst transcript7
                                    vr7
                                let cf15 ←
                                  PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                    r15
                                match cf15 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val7 =>
                                  let zc4 := index_mut_back3 val6
                                  let (_, index_mut_back4) ←
                                    Array.index_mut_usize zc4 4#usize
                                  let r16 ←
                                    r1_wire.Prefix.validated_record «prefix»
                                      8#u8
                                  let cf16 ←
                                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                      r16
                                  match cf16 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    vr8 =>
                                    let (r17, transcript9) ←
                                      r1_wire.SemanticTranscript.semantic_validated
                                        aspis_coredigestDigest32Inst
                                        transcript8 vr8
                                    let cf17 ←
                                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                        r17
                                    match cf17 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val8 =>
                                      let zc5 := index_mut_back4 val7
                                      let (_, index_mut_back5) ←
                                        Array.index_mut_usize zc5 5#usize
                                      let r18 ←
                                        r1_wire.Prefix.validated_record
                                          «prefix» 9#u8
                                      let cf18 ←
                                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                          r18
                                      match cf18 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        vr9 =>
                                        let (r19, transcript10) ←
                                          r1_wire.SemanticTranscript.semantic_validated
                                            aspis_coredigestDigest32Inst
                                            transcript9 vr9
                                        let cf19 ←
                                          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                            r19
                                        match cf19 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val9 =>
                                          let zc6 := index_mut_back5 val8
                                          let (_, index_mut_back6) ←
                                            Array.index_mut_usize zc6 6#usize
                                          let r20 ←
                                            r1_wire.Prefix.validated_record
                                              «prefix» 10#u8
                                          let cf20 ←
                                            PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                              r20
                                          match cf20 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            vr10 =>
                                            let (r21, transcript11) ←
                                              r1_wire.SemanticTranscript.semantic_validated
                                                aspis_coredigestDigest32Inst
                                                transcript10 vr10
                                            let cf21 ←
                                              PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                                r21
                                            match cf21 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val10 =>
                                              let zc7 := index_mut_back6 val9
                                              let (_, index_mut_back7) ←
                                                Array.index_mut_usize zc7
                                                  7#usize
                                              let r22 ←
                                                r1_wire.Prefix.validated_record
                                                  «prefix» 11#u8
                                              let cf22 ←
                                                PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                                  r22
                                              match cf22 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                vr11 =>
                                                let (r23, transcript12) ←
                                                  r1_wire.SemanticTranscript.semantic_validated
                                                    aspis_coredigestDigest32Inst
                                                    transcript11 vr11
                                                let cf23 ←
                                                  PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                                    r23
                                                match cf23 with
                                                |
                                                  core.ops.control_flow.ControlFlow.Continue
                                                  val11 =>
                                                  let zc8 :=
                                                    index_mut_back7 val10
                                                  let (_, index_mut_back8) ←
                                                    Array.index_mut_usize zc8
                                                      8#usize
                                                  let r24 ←
                                                    r1_wire.Prefix.validated_record
                                                      «prefix» 12#u8
                                                  let cf24 ←
                                                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                                      r24
                                                  match cf24 with
                                                  |
                                                    core.ops.control_flow.ControlFlow.Continue
                                                    vr12 =>
                                                    let (r25, transcript13) ←
                                                      r1_wire.SemanticTranscript.semantic_validated
                                                        aspis_coredigestDigest32Inst
                                                        transcript12 vr12
                                                    let cf25 ←
                                                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                                        r25
                                                    match cf25 with
                                                    |
                                                      core.ops.control_flow.ControlFlow.Continue
                                                      val12 =>
                                                      let zc9 :=
                                                        index_mut_back8 val11
                                                      let (_, index_mut_back9)
                                                        ←
                                                        Array.index_mut_usize
                                                          zc9 9#usize
                                                      let r26 ←
                                                        r1_wire.Prefix.validated_record
                                                          «prefix» 13#u8
                                                      let cf26 ←
                                                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                                          r26
                                                      match cf26 with
                                                      |
                                                        core.ops.control_flow.ControlFlow.Continue
                                                        vr13 =>
                                                        let (r27, transcript14)
                                                          ←
                                                          r1_wire.SemanticTranscript.semantic_validated
                                                            aspis_coredigestDigest32Inst
                                                            transcript13 vr13
                                                        let cf27 ←
                                                          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                                            r27
                                                        match cf27 with
                                                        |
                                                          core.ops.control_flow.ControlFlow.Continue
                                                          val13 =>
                                                          let r28 ←
                                                            r1_wire.Prefix.validated_record
                                                              «prefix» 14#u8
                                                          let cf28 ←
                                                            PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                                              r28
                                                          match cf28 with
                                                          |
                                                            core.ops.control_flow.ControlFlow.Continue
                                                            vr14 =>
                                                            let (r29,
                                                              transcript15) ←
                                                              r1_wire.SemanticTranscript.semantic_validated
                                                                aspis_coredigestDigest32Inst
                                                                transcript14
                                                                vr14
                                                            let cf29 ←
                                                              PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch
                                                                r29
                                                            match cf29 with
                                                            |
                                                              core.ops.control_flow.ControlFlow.Continue
                                                              val14 =>
                                                              let zc10 :=
                                                                index_mut_back9
                                                                  val12
                                                              ok
                                                                (core.result.Result.Ok
                                                                {
                                                                  lambda := val,
                                                                  chi := val1,
                                                                  theta := val2,
                                                                  zc := zc10,
                                                                  mu := val13,
                                                                  eta := val14
                                                                },
                                                                transcript15)
                                                            |
                                                              core.ops.control_flow.ControlFlow.Break
                                                              residual =>
                                                              let r30 ←
                                                                PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                                  aspis_core.state_only_prefix.r0.Challenges
                                                                  (core.convert.FromSame
                                                                  r1_wire.Error)
                                                                  residual
                                                              ok (r30,
                                                                transcript15)
                                                          |
                                                            core.ops.control_flow.ControlFlow.Break
                                                            residual =>
                                                            let r29 ←
                                                              PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                                aspis_core.state_only_prefix.r0.Challenges
                                                                (core.convert.FromSame
                                                                r1_wire.Error)
                                                                residual
                                                            ok (r29,
                                                              transcript14)
                                                        |
                                                          core.ops.control_flow.ControlFlow.Break
                                                          residual =>
                                                          let r28 ←
                                                            PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                              aspis_core.state_only_prefix.r0.Challenges
                                                              (core.convert.FromSame
                                                              r1_wire.Error)
                                                              residual
                                                          ok (r28,
                                                            transcript14)
                                                      |
                                                        core.ops.control_flow.ControlFlow.Break
                                                        residual =>
                                                        let r27 ←
                                                          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                            aspis_core.state_only_prefix.r0.Challenges
                                                            (core.convert.FromSame
                                                            r1_wire.Error)
                                                            residual
                                                        ok (r27, transcript13)
                                                    |
                                                      core.ops.control_flow.ControlFlow.Break
                                                      residual =>
                                                      let r26 ←
                                                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                          aspis_core.state_only_prefix.r0.Challenges
                                                          (core.convert.FromSame
                                                          r1_wire.Error)
                                                          residual
                                                      ok (r26, transcript13)
                                                  |
                                                    core.ops.control_flow.ControlFlow.Break
                                                    residual =>
                                                    let r25 ←
                                                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                        aspis_core.state_only_prefix.r0.Challenges
                                                        (core.convert.FromSame
                                                        r1_wire.Error) residual
                                                    ok (r25, transcript12)
                                                |
                                                  core.ops.control_flow.ControlFlow.Break
                                                  residual =>
                                                  let r24 ←
                                                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                      aspis_core.state_only_prefix.r0.Challenges
                                                      (core.convert.FromSame
                                                      r1_wire.Error) residual
                                                  ok (r24, transcript12)
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                let r23 ←
                                                  PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                    aspis_core.state_only_prefix.r0.Challenges
                                                    (core.convert.FromSame
                                                    r1_wire.Error) residual
                                                ok (r23, transcript11)
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              let r22 ←
                                                PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                  aspis_core.state_only_prefix.r0.Challenges
                                                  (core.convert.FromSame
                                                  r1_wire.Error) residual
                                              ok (r22, transcript11)
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            let r21 ←
                                              PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                aspis_core.state_only_prefix.r0.Challenges
                                                (core.convert.FromSame
                                                r1_wire.Error) residual
                                            ok (r21, transcript10)
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          let r20 ←
                                            PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                              aspis_core.state_only_prefix.r0.Challenges
                                              (core.convert.FromSame
                                              r1_wire.Error) residual
                                          ok (r20, transcript10)
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        let r19 ←
                                          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                            aspis_core.state_only_prefix.r0.Challenges
                                            (core.convert.FromSame
                                            r1_wire.Error) residual
                                        ok (r19, transcript9)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      let r18 ←
                                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                          aspis_core.state_only_prefix.r0.Challenges
                                          (core.convert.FromSame r1_wire.Error)
                                          residual
                                      ok (r18, transcript9)
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    let r17 ←
                                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                        aspis_core.state_only_prefix.r0.Challenges
                                        (core.convert.FromSame r1_wire.Error)
                                        residual
                                    ok (r17, transcript8)
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  let r16 ←
                                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                      aspis_core.state_only_prefix.r0.Challenges
                                      (core.convert.FromSame r1_wire.Error)
                                      residual
                                  ok (r16, transcript8)
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                let r15 ←
                                  PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                    aspis_core.state_only_prefix.r0.Challenges
                                    (core.convert.FromSame r1_wire.Error)
                                    residual
                                ok (r15, transcript7)
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              let r14 ←
                                PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                  aspis_core.state_only_prefix.r0.Challenges
                                  (core.convert.FromSame r1_wire.Error)
                                  residual
                              ok (r14, transcript7)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            let r13 ←
                              PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                aspis_core.state_only_prefix.r0.Challenges
                                (core.convert.FromSame r1_wire.Error) residual
                            ok (r13, transcript6)
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          let r12 ←
                            PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                              aspis_core.state_only_prefix.r0.Challenges
                              (core.convert.FromSame r1_wire.Error) residual
                          ok (r12, transcript6)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        let r11 ←
                          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            aspis_core.state_only_prefix.r0.Challenges
                            (core.convert.FromSame r1_wire.Error) residual
                        ok (r11, transcript5)
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      let r10 ←
                        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          aspis_core.state_only_prefix.r0.Challenges
                          (core.convert.FromSame r1_wire.Error) residual
                      ok (r10, transcript5)
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    let r9 ←
                      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        aspis_core.state_only_prefix.r0.Challenges
                        (core.convert.FromSame r1_wire.Error) residual
                    ok (r9, transcript4)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  let r8 ←
                    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      aspis_core.state_only_prefix.r0.Challenges
                      (core.convert.FromSame r1_wire.Error) residual
                  ok (r8, transcript4)
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r7 ←
                  PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    aspis_core.state_only_prefix.r0.Challenges
                    (core.convert.FromSame r1_wire.Error) residual
                ok (r7, transcript3)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r6 ←
                PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  aspis_core.state_only_prefix.r0.Challenges
                  (core.convert.FromSame r1_wire.Error) residual
              ok (r6, transcript3)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ←
              PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                aspis_core.state_only_prefix.r0.Challenges
                (core.convert.FromSame r1_wire.Error) residual
            ok (r5, transcript2)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              aspis_core.state_only_prefix.r0.Challenges (core.convert.FromSame
              r1_wire.Error) residual
          ok (r4, transcript2)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            aspis_core.state_only_prefix.r0.Challenges (core.convert.FromSame
            r1_wire.Error) residual
        ok (r3, transcript1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          aspis_core.state_only_prefix.r0.Challenges (core.convert.FromSame
          r1_wire.Error) residual
      ok (r2, transcript1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        aspis_core.state_only_prefix.r0.Challenges (core.convert.FromSame
        r1_wire.Error) residual
    ok (r1, transcript)

end AspisR1PublicPreparationPIN2

set_option maxHeartbeats 200000

/-! Section 2: PrefixAdapter (scripted copy of ExtractedPrefixParseCore with the PIN2 namespace). -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparationPIN2.PrefixAdapter
open r1_wire
abbrev OldPrefix := AspisR1PrefixAggregateParser.r1_wire.Prefix
abbrev OldError := AspisR1PrefixAggregateParser.r1_wire.Error

def toOld (pre : Prefix) : OldPrefix := ⟨pre.c1_root, pre.records⟩
def fromOld (pre : OldPrefix) : Prefix := ⟨pre.c1_root, pre.records⟩
@[simp] theorem toOld_fromOld (pre : OldPrefix) : toOld (fromOld pre) = pre := by cases pre; rfl
@[simp] theorem fromOld_toOld (pre : Prefix) : fromOld (toOld pre) = pre := by cases pre; rfl

def errorFromOld : OldError → r1_wire.Error
  | .Allocation => .Allocation
  | .RowOrder expected actual => .RowOrder expected actual
  | .InvalidRow => .InvalidRow
  | .Tag row => .Tag row
  | .Length row => .Length row
  | .NonCanonical row value => .NonCanonical row value
  | .Boundary value => .Boundary value
  | .Terminal => .Terminal
  | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes
  | .Public => .Public

/-- A fixed actual parser, with only its nominal Prefix/Error carriers mapped.
This definition can instantiate an explicit downstream caller boundary. -/
def parseAccepted (bytes : Slice U8) : Result (core.result.Result Prefix r1_wire.Error) := do
  let result ← AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes
  match result with
  | .Ok pre => ok (.Ok (fromOld pre))
  | .Err error => ok (.Err (errorFromOld error))

theorem parse_success (bytes : Slice U8) (pre : Prefix)
    (h : parseAccepted bytes = ok (.Ok pre)) :
    AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes = ok (.Ok (toOld pre)) := by
  unfold parseAccepted at h
  cases hp : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
  | fail error => simp only [hp, bind_tc_fail] at h; cases h
  | div => simp only [hp, bind_tc_div] at h; cases h
  | ok result =>
    cases result with
    | Err error => simp only [hp, bind_tc_ok] at h; cases h
    | Ok old =>
      simp only [hp, bind_tc_ok] at h
      have he : fromOld old = pre := core.result.Result.Ok.inj (Result.ok.inj h)
      have ho : old = toOld pre := by rw [← he]; rfl
      simpa only [ho] using hp

#print axioms parseAccepted
#print axioms parse_success
end AspisR1PublicPreparationPIN2.PrefixAdapter

namespace AspisR1PublicPreparationPIN2

/-! Section 3: VerifyPrefix (PW8_SUBSTITUTION.json). -/
abbrev VerifyPrefix.Finish := {H : Type _} → aspis_core.digest.Digest32 H →
  pool_v1.pair_forest_semantic_terminal.r0.Public → r1_wire.Prefix → (r1_wire.SemanticTranscript H) → aspis_core.state_only_prefix.r0.Challenges → (Option (RPz7_PhaseIso.Phase → Result Unit)) → Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)

def VerifyPrefix.mark
  (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (i : Std.U8) :
  Result Unit
  := do
  ok ()

def VerifyPrefix.verify (F : VerifyPrefix.Finish)
  {H : Type _} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  («public» : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (bytes : Slice Std.U8) (hash : H)
  (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
  Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
  := do
  let r ← PrefixAdapter.parseAccepted bytes
  let cf ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue p =>
    VerifyPrefix.mark obs 0#u8
    let r1 ←
      r1_semantic.public_transcript aspis_coredigestDigest32Inst «public» hash
        p.c1_root
    let cf1 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r2, val1) ← r1_wire.begin aspis_coredigestDigest32Inst p val
      let cf2 ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        VerifyPrefix.mark obs 1#u8
        F aspis_coredigestDigest32Inst «public» p val1
          val2 obs
      | core.ops.control_flow.ControlFlow.Break residual =>
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual

end AspisR1PublicPreparationPIN2

#print axioms AspisR1PublicPreparationPIN2.r1_wire.begin
#print axioms AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.semantic_validated
#print axioms AspisR1PublicPreparationPIN2.PrefixAdapter.parseAccepted
#print axioms AspisR1PublicPreparationPIN2.VerifyPrefix.mark
#print axioms AspisR1PublicPreparationPIN2.VerifyPrefix.verify
