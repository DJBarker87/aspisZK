import R1Z.ProverRwRngOwnerEvents
import R1Z.ProverRwRngTape
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngOwnerDraw
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
open ProverRwRngOwnerStep ProverRwRngOwnerEvents
variable [ErasureFns]
def afterFill (mask_nonce : Array U8 32#usize) (retry : Usize)
    (reply : (Tape × core.result.Result Unit U8) × Array U8 64#usize) :
    Result (ControlFlow State (Tape × Status)) := do
  let ((after,result),a2) := reply
  let bytes1 := a2
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
      ok (done (after, core.result.Result.Err (StateOnlyAttemptEntropyError.Os
        e)))

theorem draw_factor (nonce : Array U8 32#usize) (p : Tape) (retry : Usize) :
    newBody nonce (p,retry) =
      if retry < 16#usize then
        (Tape.Insts.Prover_rw_rng_preflightDraw64.fill p (Array.repeat 64#usize 0#u8) >>=
          afterFill nonce retry)
      else .ok (.done (p,.Err .RepeatedZeroBlock)) := by
  unfold newBody StateOnlyAttemptSecrets.generate_with_loop.body
  split
  · simp only [zeroize.Zeroizing.new,
      zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,bind_tc_ok,Aeneas.Std.uncurry]
    rfl
  · rfl
#print axioms draw_factor
end R1Z.ProverRwRngOwnerDraw
