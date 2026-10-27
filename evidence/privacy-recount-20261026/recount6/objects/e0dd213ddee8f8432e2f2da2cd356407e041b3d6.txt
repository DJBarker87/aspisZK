import R1Z.ProverRwRngEmission
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace ProverRwRng
variable [ErasureFns]
/-- [prover_rw_rng_owner::{impl core::convert::From<u8> for prover_rw_rng_owner::StateOnlyAttemptEntropyError}::from]:
    Source: 'lib.rs', lines 71:49-71:84
    Visibility: public -/
def StateOnlyAttemptEntropyError.Insts.CoreConvertFromU8.from
  (e : Std.U8) : Result StateOnlyAttemptEntropyError := do
  ok (StateOnlyAttemptEntropyError.Os e)

/-- Trait implementation: [prover_rw_rng_owner::{impl core::convert::From<u8> for prover_rw_rng_owner::StateOnlyAttemptEntropyError}]
    Source: 'lib.rs', lines 71:0-71:86 -/
@[reducible]
def StateOnlyAttemptEntropyError.Insts.CoreConvertFromU8 : core.convert.From
  StateOnlyAttemptEntropyError Std.U8 := {
  «from» := StateOnlyAttemptEntropyError.Insts.CoreConvertFromU8.from
}

/-- [prover_rw_rng_owner::{prover_rw_rng_owner::Tape}::draw]:
    Source: 'lib.rs', lines 74:4-80:5 -/
def Tape.draw
  (self : Tape) (bytes : Array Std.U8 64#usize) :
  Result ((core.result.Result Unit Std.U8) × Tape × (Array Std.U8 64#usize))
  := do
  let i := alloc.vec.Vec.len self.replies
  massert (self.used < i)
  let (block, result) ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice ((Array Std.U8
      64#usize) × (core.result.Result Unit Std.U8))) self.replies self.used
  let i1 ← self.used + 1#usize
  ok (result, { self with used := i1 }, block)

/-- [prover_rw_rng_owner::{prover_rw_rng_owner::StateOnlyAttemptSecrets}::old]: loop body 0:
    Source: 'lib.rs', lines 1:0-111:5
    Visibility: public -/
@[rust_loop_body]
def StateOnlyAttemptSecrets.old_loop.body
  (mask_nonce : Array Std.U8 32#usize) (limit : Std.Usize) (tape : Tape)
  (retry : Std.Usize) :
  Result (ControlFlow (Tape × Std.Usize) ((core.result.Result
    StateOnlyAttemptSecrets StateOnlyAttemptEntropyError) × Tape))
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
    let (r, tape1, a2) ← Tape.draw tape a1
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let bytes1 := deref_mut_back a2
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
          ok (done (core.result.Result.Ok
            {
              mask_nonce,
              field_mask_entropy := field_mask_entropy1,
              leaf_salt_seed := leaf_salt_seed1
            }, tape1))
        else let retry1 ← retry + 1#usize
             ok (cont (tape1, retry1))
      else let retry1 ← retry + 1#usize
           ok (cont (tape1, retry1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          StateOnlyAttemptSecrets
          StateOnlyAttemptEntropyError.Insts.CoreConvertFromU8 residual
      ok (done (r1, tape1))
  else
    ok (done (core.result.Result.Err
      StateOnlyAttemptEntropyError.RepeatedZeroBlock, tape))

/-- [prover_rw_rng_owner::{prover_rw_rng_owner::StateOnlyAttemptSecrets}::old]: loop 0:
    Source: 'lib.rs', lines 1:0-111:5
    Visibility: public -/
@[rust_loop]
def StateOnlyAttemptSecrets.old_loop
  (mask_nonce : Array Std.U8 32#usize) (tape : Tape) (limit : Std.Usize)
  (retry : Std.Usize) :
  Result ((core.result.Result StateOnlyAttemptSecrets
    StateOnlyAttemptEntropyError) × Tape)
  := do
  loop
    (fun (tape1, retry1) => StateOnlyAttemptSecrets.old_loop.body mask_nonce
      limit tape1 retry1)
    (tape, retry)

/-- [prover_rw_rng_owner::{prover_rw_rng_owner::StateOnlyAttemptSecrets}::old]:
    Source: 'lib.rs', lines 83:4-111:5
    Visibility: public -/
def StateOnlyAttemptSecrets.old
  (mask_nonce : Array Std.U8 32#usize) (tape : Tape) :
  Result ((core.result.Result StateOnlyAttemptSecrets
    StateOnlyAttemptEntropyError) × Tape)
  := do
  let b ← entropy_nonzero32 mask_nonce
  if b
  then
    StateOnlyAttemptSecrets.old_loop mask_nonce tape ENTROPY_RETRY_LIMIT
      0#usize
  else
    ok (core.result.Result.Err StateOnlyAttemptEntropyError.RepeatedZeroBlock,
      tape)

/-- [prover_rw_rng_owner::old_owner]:
    Source: 'lib.rs', lines 114:0-117:1
    Visibility: public -/
def old_owner
  (nonce : Array Std.U8 32#usize) (tape : Tape) :
  Result (Tape × (core.result.Result StateOnlyAttemptSecrets
    StateOnlyAttemptEntropyError))
  := do
  let (status, tape1) ← StateOnlyAttemptSecrets.old nonce tape
  ok (tape1, status)

end ProverRwRng
