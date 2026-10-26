import Aeneas
open Aeneas Aeneas.Std Result ControlFlow
noncomputable section
namespace ProverRwRngCaller
class NativeTypes where
  inner : Type
  nonzero : Type → Type → Type
abbrev core.num.niche_types.NonZeroI32Inner [NativeTypes] := NativeTypes.inner
abbrev core.num.nonzero.NonZero [NativeTypes] := NativeTypes.nonzero
variable [NativeTypes]
end ProverRwRngCaller
namespace ProverRwRngCaller
variable [NativeTypes]

/-- [getrandom::error::Error]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/getrandom-0.3.4/src/error.rs', lines 36:0-36:16
    Name pattern: [getrandom::error::Error]
    Visibility: public -/
@[reducible, rust_type "getrandom::error::Error"]
def getrandom.error.Error :=
  core.num.nonzero.NonZero Std.I32 core.num.niche_types.NonZeroI32Inner

/-- Trait declaration: [zeroize::Zeroize]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.1/src/lib.rs', lines 245:0-245:17
    Name pattern: [zeroize::Zeroize]
    Visibility: public -/
@[rust_trait "zeroize::Zeroize"]
structure zeroize.Zeroize (Self : Type) where
  zeroize : Self → Result Self

/-- Trait declaration: [zeroize::DefaultIsZeroes]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.1/src/lib.rs', lines 255:0-255:49
    Name pattern: [zeroize::DefaultIsZeroes]
    Visibility: public -/
@[rust_trait "zeroize::DefaultIsZeroes"
  (parentClauses := ["coremarkerCopyInst", "coredefaultDefaultInst"])]
structure zeroize.DefaultIsZeroes (Self : Type) where
  coremarkerCopyInst : core.marker.Copy Self
  coredefaultDefaultInst : core.default.Default Self

/-- [zeroize::Zeroizing]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.1/src/lib.rs', lines 599:0-599:41
    Name pattern: [zeroize::Zeroizing]
    Visibility: public -/
@[reducible, rust_type "zeroize::Zeroizing"]
def zeroize.Zeroizing (Z : Type) := Z

/-- [prover_rw_rng_caller::StateOnlyAttemptEntropyError]
    Source: 'lib.rs', lines 5:0-5:81
    Visibility: public -/
inductive StateOnlyAttemptEntropyError where
| Os : getrandom.error.Error → StateOnlyAttemptEntropyError
| RepeatedZeroBlock : StateOnlyAttemptEntropyError

/-- [prover_rw_rng_caller::StateOnlyAttemptSecrets]
    Source: 'lib.rs', lines 6:0-10:1
    Visibility: public -/
structure StateOnlyAttemptSecrets where
  mask_nonce : Array Std.U8 32#usize
  field_mask_entropy : zeroize.Zeroizing (Array Std.U8 32#usize)
  leaf_salt_seed : zeroize.Zeroizing (Array Std.U8 32#usize)

/-- Trait declaration: [prover_rw_rng_caller::Draw64]
    Source: 'lib.rs', lines 11:0-13:1
    Visibility: public -/
structure Draw64 (Self : Type) where
  fill : Self → (Array Std.U8 64#usize) → Result ((Self ×
    (core.result.Result Unit getrandom.error.Error)) × (Array Std.U8
    64#usize))

/-- [prover_rw_rng_caller::Tape]
    Source: 'lib.rs', lines 15:0-15:93
    Visibility: public -/
structure Tape where
  replies : alloc.vec.Vec ((Array Std.U8 64#usize) × (core.result.Result Unit
    getrandom.error.Error))
  used : Std.Usize

/-- [prover_rw_rng_caller::Error]
    Source: 'lib.rs', lines 74:0-75:40
    Visibility: public -/
inductive Error where
| Parse : Error
| Semantic : Error
| Transcript : Error
| Relation : Error
| Merkle : Error
| Query : Error
| Checkpoint : Error
| Allocation : Error
| Rejected : Error
| AttemptsExhausted : Error
| Entropy : Error

/-- [prover_rw_rng_caller::RetriedProof]
    Source: 'lib.rs', lines 76:0-76:80
    Visibility: public -/
structure RetriedProof where
  proof : alloc.vec.Vec Std.U8
  audit : Std.U64
  attempts : Std.Usize

/-- [prover_rw_rng_caller::selected_callback::closure]
    Source: 'lib.rs', lines 84:39-84:56 -/
@[reducible]
def selected_callback.closure (N : Type) := Unit



-- Unused erasure callbacks stay explicit parameters. Their runtime/drop
-- semantics are not asserted by this value-level installation.
class ErasureFns where
  scalar : {Z : Type} → zeroize.DefaultIsZeroes Z → Z → Result Z
  array : {Z : Type} → {N : Usize} → zeroize.Zeroize Z → Array Z N → Result (Array Z N)
variable [ErasureFns]
def zeroize.Zeroize.Blanket.zeroize {Z : Type} (d : zeroize.DefaultIsZeroes Z) : Z → Result Z := ErasureFns.scalar d
def Array.Insts.ZeroizeZeroize.zeroize {Z : Type} {N : Usize} (d : zeroize.Zeroize Z) : Array Z N → Result (Array Z N) := ErasureFns.array d
-- Value-level transparent new/deref installation, not a physical drop theorem.
def zeroize.Zeroizing.new {Z : Type} (_ : zeroize.Zeroize Z) (z : Z) : Result (zeroize.Zeroizing Z) := .ok z
def zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref {Z : Type} (_ : zeroize.Zeroize Z) (z : zeroize.Zeroizing Z) : Result Z := .ok z
def zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut {Z : Type} (_ : zeroize.Zeroize Z) (z : zeroize.Zeroizing Z) : Result (Z × (Z → zeroize.Zeroizing Z)) := .ok (z,id)

def core.result.Result.map_err {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F)
    (status : core.result.Result T E) (closure : O) : Result (core.result.Result T F) :=
  match status with
  | .Ok x => .ok (.Ok x)
  | .Err e => do
    let mapped ← inst.call_once closure e
    .ok (.Err mapped)
/-- Trait implementation: [zeroize::{impl zeroize::Zeroize for Z}]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.1/src/lib.rs', lines 270:0-272:23
    Name pattern: [zeroize::Zeroize<@Z>] -/
@[reducible, rust_trait_impl "zeroize::Zeroize<@Z>"]
def zeroize.Zeroize.Blanket {Z : Type} (DefaultIsZeroesInst :
  zeroize.DefaultIsZeroes Z) : zeroize.Zeroize Z := {
  zeroize := zeroize.Zeroize.Blanket.zeroize DefaultIsZeroesInst
}

/-- Trait implementation: [zeroize::{impl zeroize::DefaultIsZeroes for u8}]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.1/src/lib.rs', lines 281:10-281:40
    Name pattern: [zeroize::DefaultIsZeroes<u8>] -/
@[reducible, rust_trait_impl "zeroize::DefaultIsZeroes<u8>"]
def U8.Insts.ZeroizeDefaultIsZeroes : zeroize.DefaultIsZeroes Std.U8 := {
  coremarkerCopyInst := core.marker.CopyU8
  coredefaultDefaultInst := core.default.DefaultU8
}

/-- Trait implementation: [zeroize::{impl zeroize::Zeroize for [Z; N]}]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.1/src/lib.rs', lines 340:0-342:15
    Name pattern: [zeroize::Zeroize<[@Z; @N]>] -/
@[reducible, rust_trait_impl "zeroize::Zeroize<[@Z; @N]>"]
def Array.Insts.ZeroizeZeroize {Z : Type} (N : Std.Usize) (ZeroizeInst :
  zeroize.Zeroize Z) : zeroize.Zeroize (Array Z N) := {
  zeroize := Array.Insts.ZeroizeZeroize.zeroize ZeroizeInst
}

/-- [prover_rw_rng_caller::ENTROPY_RETRY_LIMIT]
    Source: 'lib.rs', lines 3:0-3:38 -/
@[global_simps, irreducible] def ENTROPY_RETRY_LIMIT : Std.Usize := 16#usize

/-- [prover_rw_rng_caller::{impl prover_rw_rng_caller::Draw64 for prover_rw_rng_caller::Tape}::fill]:
    Source: 'lib.rs', lines 17:4-23:5
    Visibility: public -/
def Tape.Insts.Prover_rw_rng_callerDraw64.fill
  (self : Tape) (bytes : Array Std.U8 64#usize) :
  Result ((Tape × (core.result.Result Unit getrandom.error.Error)) × (Array
    Std.U8 64#usize))
  := do
  let i := alloc.vec.Vec.len self.replies
  massert (self.used < i)
  let (block, result) ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice ((Array Std.U8
      64#usize) × (core.result.Result Unit getrandom.error.Error)))
      self.replies self.used
  let i1 ← self.used + 1#usize
  ok (({ self with used := i1 }, result), block)

/-- Trait implementation: [prover_rw_rng_caller::{impl prover_rw_rng_caller::Draw64 for prover_rw_rng_caller::Tape}]
    Source: 'lib.rs', lines 16:0-24:1 -/
@[reducible]
def Tape.Insts.Prover_rw_rng_callerDraw64 : Draw64 Tape := {
  fill := Tape.Insts.Prover_rw_rng_callerDraw64.fill
}

/-- [prover_rw_rng_caller::entropy_nonzero32]: loop body 0:
    Source: 'lib.rs', lines 31:4-31:41 -/
@[rust_loop_body]
def entropy_nonzero32_loop.body
  (bytes : Array Std.U8 32#usize) (combined : Std.U8) (i : Std.Usize) :
  Result (ControlFlow (Std.U8 × Std.Usize) Std.U8)
  := do
  if i < 32#usize
  then
    let i1 ← Array.index_usize bytes i
    let combined1 ← lift (combined ||| i1)
    let i2 ← i + 1#usize
    ok (cont (combined1, i2))
  else ok (done combined)

/-- [prover_rw_rng_caller::entropy_nonzero32]: loop 0:
    Source: 'lib.rs', lines 31:4-31:41 -/
@[rust_loop]
def entropy_nonzero32_loop
  (bytes : Array Std.U8 32#usize) (combined : Std.U8) (i : Std.Usize) :
  Result Std.U8
  := do
  loop
    (fun (combined1, i1) => entropy_nonzero32_loop.body bytes combined1 i1)
    (combined, i)

/-- [prover_rw_rng_caller::entropy_nonzero32]:
    Source: 'lib.rs', lines 29:0-33:1 -/
def entropy_nonzero32 (bytes : Array Std.U8 32#usize) : Result Bool := do
  let combined ← entropy_nonzero32_loop bytes 0#u8 0#usize
  ok (combined != 0#u8)

/-- [prover_rw_rng_caller::{impl core::convert::From<getrandom::error::Error> for prover_rw_rng_caller::StateOnlyAttemptEntropyError}::from]:
    Source: 'lib.rs', lines 71:4-71:64
    Visibility: public -/
def StateOnlyAttemptEntropyError.Insts.CoreConvertFromError.from
  (value : getrandom.error.Error) : Result StateOnlyAttemptEntropyError := do
  ok (StateOnlyAttemptEntropyError.Os value)

/-- [prover_rw_rng_caller::{prover_rw_rng_caller::StateOnlyAttemptSecrets}::generate_with]: loop body 0:
    Source: 'lib.rs', lines 1:0-66:5
    Visibility: public -/
@[rust_loop_body]
def StateOnlyAttemptSecrets.generate_with_loop.body
  {P : Type} (Draw64Inst : Draw64 P) (mask_nonce : Array Std.U8 32#usize)
  (limit : Std.Usize) (provider : P) (retry : Std.Usize) :
  Result (ControlFlow (P × Std.Usize) (P × (core.result.Result
    StateOnlyAttemptSecrets StateOnlyAttemptEntropyError)))
  := do
  if retry < limit
  then
    let a := Array.repeat 64#usize 0#u8
    let bytes ←
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 64#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a
    let (a1, deref_mut_back) ←
      zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut
        (Array.Insts.ZeroizeZeroize 64#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) bytes
    let ((after, result), a2) ← Draw64Inst.fill provider a1
    let bytes1 := deref_mut_back a2
    match result with
    | core.result.Result.Ok _ =>
      let a3 := Array.repeat 32#usize 0#u8
      let field_mask_entropy ←
        zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a3
      let a4 := Array.repeat 32#usize 0#u8
      let leaf_salt_seed ←
        zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a4
      let (a5, deref_mut_back1) ←
        zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) field_mask_entropy
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut a5)
      let a6 ←
        zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
          (Array.Insts.ZeroizeZeroize 64#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) bytes1
      let s1 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) a6
          { «end» := 32#usize }
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let a7 := to_slice_mut_back s2
      let field_mask_entropy1 := deref_mut_back1 a7
      let (a8, deref_mut_back2) ←
        zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) leaf_salt_seed
      let (s3, to_slice_mut_back1) ← lift (Array.to_slice_mut a8)
      let s4 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) a6
          { start := 32#usize }
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
      let a9 := to_slice_mut_back1 s5
      let leaf_salt_seed1 := deref_mut_back2 a9
      let a10 ←
        zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) field_mask_entropy1
      let b ← entropy_nonzero32 a10
      if b
      then
        let a11 ←
          zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
            (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
            U8.Insts.ZeroizeDefaultIsZeroes)) leaf_salt_seed1
        let b1 ← entropy_nonzero32 a11
        if b1
        then
          ok (done (after, core.result.Result.Ok
            {
              mask_nonce,
              field_mask_entropy := field_mask_entropy1,
              leaf_salt_seed := leaf_salt_seed1
            }))
        else let retry1 ← retry + 1#usize
             ok (cont (after, retry1))
      else let retry1 ← retry + 1#usize
           ok (cont (after, retry1))
    | core.result.Result.Err e =>
      let soaee ←
        StateOnlyAttemptEntropyError.Insts.CoreConvertFromError.from e
      ok (done (after, core.result.Result.Err soaee))
  else
    ok (done (provider, core.result.Result.Err
      StateOnlyAttemptEntropyError.RepeatedZeroBlock))

/-- [prover_rw_rng_caller::{prover_rw_rng_caller::StateOnlyAttemptSecrets}::generate_with]: loop 0:
    Source: 'lib.rs', lines 1:0-66:5
    Visibility: public -/
@[rust_loop]
def StateOnlyAttemptSecrets.generate_with_loop
  {P : Type} (Draw64Inst : Draw64 P) (mask_nonce : Array Std.U8 32#usize)
  (provider : P) (limit : Std.Usize) (retry : Std.Usize) :
  Result (P × (core.result.Result StateOnlyAttemptSecrets
    StateOnlyAttemptEntropyError))
  := do
  loop
    (fun (provider1, retry1) => StateOnlyAttemptSecrets.generate_with_loop.body
      Draw64Inst mask_nonce limit provider1 retry1)
    (provider, retry)

/-- [prover_rw_rng_caller::{prover_rw_rng_caller::StateOnlyAttemptSecrets}::generate_with]:
    Source: 'lib.rs', lines 36:4-66:5
    Visibility: public -/
def StateOnlyAttemptSecrets.generate_with
  {P : Type} (Draw64Inst : Draw64 P) (mask_nonce : Array Std.U8 32#usize)
  (provider : P) :
  Result (P × (core.result.Result StateOnlyAttemptSecrets
    StateOnlyAttemptEntropyError))
  := do
  let b ← entropy_nonzero32 mask_nonce
  if b
  then
    StateOnlyAttemptSecrets.generate_with_loop Draw64Inst mask_nonce provider
      ENTROPY_RETRY_LIMIT 0#usize
  else
    ok (provider, core.result.Result.Err
      StateOnlyAttemptEntropyError.RepeatedZeroBlock)

/-- [prover_rw_rng_caller::ATTEMPT_CAP]
    Source: 'lib.rs', lines 77:0-77:30
    Visibility: public -/
@[global_simps, irreducible] def ATTEMPT_CAP : Std.Usize := 8#usize

/-- [prover_rw_rng_caller::selected_callback::{impl core::ops::function::FnOnce<(prover_rw_rng_caller::StateOnlyAttemptEntropyError,), prover_rw_rng_caller::Error> for prover_rw_rng_caller::selected_callback::closure<N>}::call_once]:
    Source: 'lib.rs', lines 84:39-84:56 -/
def
  selected_callback.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError.call_once
  {N : Type} (coreopsfunctionFnMutNTupleUsizeArrayU832Inst :
  core.ops.function.FnMut N Std.Usize (Array Std.U8 32#usize))
  (c : selected_callback.closure N)
  (tupled_args : StateOnlyAttemptEntropyError) :
  Result Error
  := do
  ok Error.Entropy

/-- Trait implementation: [prover_rw_rng_caller::selected_callback::{impl core::ops::function::FnOnce<(prover_rw_rng_caller::StateOnlyAttemptEntropyError,), prover_rw_rng_caller::Error> for prover_rw_rng_caller::selected_callback::closure<N>}]
    Source: 'lib.rs', lines 84:39-84:56 -/
@[reducible]
def
  selected_callback.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError
  {N : Type} (coreopsfunctionFnMutNTupleUsizeArrayU832Inst :
  core.ops.function.FnMut N Std.Usize (Array Std.U8 32#usize)) :
  core.ops.function.FnOnce (selected_callback.closure N)
  StateOnlyAttemptEntropyError Error := {
  call_once :=
    selected_callback.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError.call_once
    coreopsfunctionFnMutNTupleUsizeArrayU832Inst
}

/-- [prover_rw_rng_caller::selected_callback]:
    Source: 'lib.rs', lines 79:0-85:1
    Visibility: public -/
def selected_callback
  {N : Type} (coreopsfunctionFnMutNTupleUsizeArrayU832Inst :
  core.ops.function.FnMut N Std.Usize (Array Std.U8 32#usize)) (tape : Tape)
  (proof_account : N) (k : Std.Usize) :
  Result (Tape × N × (core.result.Result StateOnlyAttemptSecrets Error))
  := do
  let (nonce, proof_account1) ←
    coreopsfunctionFnMutNTupleUsizeArrayU832Inst.call_mut proof_account k
  let (tape1, status) ←
    StateOnlyAttemptSecrets.generate_with Tape.Insts.Prover_rw_rng_callerDraw64
      nonce tape
  let r ←
    core.result.Result.map_err
      (selected_callback.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError
      coreopsfunctionFnMutNTupleUsizeArrayU832Inst) status ()
  ok (tape1, proof_account1, r)

/-- [prover_rw_rng_caller::retry_attempt]:
    Source: 'lib.rs', lines 86:0-100:1
    Visibility: public -/
def retry_attempt
  {N : Type} {L : Type} {B : Type}
  (coreopsfunctionFnMutNTupleUsizeArrayU832Inst : core.ops.function.FnMut N
  Std.Usize (Array Std.U8 32#usize))
  (coreopsfunctionFnMutBPairStateOnlyAttemptSecretsLPairLResultPairVecU8U64ErrorInst
  : core.ops.function.FnMut B (StateOnlyAttemptSecrets × L) (L ×
  (core.result.Result ((alloc.vec.Vec Std.U8) × Std.U64) Error)))
  (tape : Tape) (proof_account : N) (nonce_store : L) (body : B)
  (k : Std.Usize) :
  Result (Tape × N × L × B × (core.result.Result RetriedProof Error))
  := do
  if k >= ATTEMPT_CAP
  then
    ok (tape, proof_account, nonce_store, body, core.result.Result.Err
      Error.AttemptsExhausted)
  else
    let (tape1, proof_account1, status) ←
      selected_callback coreopsfunctionFnMutNTupleUsizeArrayU832Inst tape
        proof_account k
    match status with
    | core.result.Result.Ok a =>
      let ((after_store, result), body1) ←
        coreopsfunctionFnMutBPairStateOnlyAttemptSecretsLPairLResultPairVecU8U64ErrorInst.call_mut
          body (a, nonce_store)
      match result with
      | core.result.Result.Ok p =>
        let (proof, audit) := p
        let i ← k + 1#usize
        ok (tape1, proof_account1, after_store, body1, core.result.Result.Ok
          { proof, audit, attempts := i })
      | core.result.Result.Err e =>
        match e with
        | Error.Parse =>
          ok (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Parse)
        | Error.Semantic =>
          ok (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Semantic)
        | Error.Transcript =>
          ok (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Transcript)
        | Error.Relation =>
          ok (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Relation)
        | Error.Merkle =>
          ok (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Merkle)
        | Error.Query =>
          ok (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Query)
        | Error.Checkpoint =>
          ok (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Checkpoint)
        | Error.Allocation =>
          ok (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Allocation)
        | Error.Rejected =>
          let i ← k + 1#usize
          retry_attempt coreopsfunctionFnMutNTupleUsizeArrayU832Inst
            coreopsfunctionFnMutBPairStateOnlyAttemptSecretsLPairLResultPairVecU8U64ErrorInst
            tape1 proof_account1 after_store body1 i
        | Error.AttemptsExhausted =>
          ok (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.AttemptsExhausted)
        | Error.Entropy =>
          ok (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Entropy)
    | core.result.Result.Err e =>
      ok (tape1, proof_account1, nonce_store, body, core.result.Result.Err e)
partial_fixpoint

/-- [prover_rw_rng_caller::prove_masked_retrying_with]:
    Source: 'lib.rs', lines 101:0-107:1
    Visibility: public -/
def prove_masked_retrying_with
  {N : Type} {L : Type} {B : Type}
  (coreopsfunctionFnMutNTupleUsizeArrayU832Inst : core.ops.function.FnMut N
  Std.Usize (Array Std.U8 32#usize))
  (coreopsfunctionFnMutBPairStateOnlyAttemptSecretsLPairLResultPairVecU8U64ErrorInst
  : core.ops.function.FnMut B (StateOnlyAttemptSecrets × L) (L ×
  (core.result.Result ((alloc.vec.Vec Std.U8) × Std.U64) Error)))
  (is_s2 : Bool) (tape : Tape) (proof_account : N) (nonce_store : L) 
  (body : B) :
  Result (Tape × N × L × B × (core.result.Result RetriedProof Error))
  := do
  if is_s2
  then
    retry_attempt coreopsfunctionFnMutNTupleUsizeArrayU832Inst
      coreopsfunctionFnMutBPairStateOnlyAttemptSecretsLPairLResultPairVecU8U64ErrorInst
      tape proof_account nonce_store body 0#usize
  else
    ok (tape, proof_account, nonce_store, body, core.result.Result.Err
      Error.Semantic)

end ProverRwRngCaller
