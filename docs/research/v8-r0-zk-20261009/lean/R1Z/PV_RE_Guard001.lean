import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Guard001
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def onTrue (mask_nonce : Array Std.U8 32#usize) (limit : Std.Usize) (retry : Std.Usize) : Result (ControlFlow Std.Usize (core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
    aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError)) := do
    let a := Array.repeat 64#usize 0#u8
    let bytes ←
      zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 64#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a
    let (s, as_mut_back) ←
      zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut
        (Array.Insts.CoreConvertAsMutSlice Std.U8 64#usize)
        (Array.Insts.ZeroizeZeroize 64#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) bytes
    let (r, s1) ← getrandom.fill s
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let bytes1 := as_mut_back s1
      let a1 := Array.repeat 32#usize 0#u8
      let field_mask_entropy ←
        zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a1
      let a2 := Array.repeat 32#usize 0#u8
      let leaf_salt_seed ←
        zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a2
      let (a3, deref_mut_back) ←
        zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) field_mask_entropy
      let (s2, to_slice_mut_back) ← Aeneas.Std.lift (Array.to_slice_mut a3)
      let a4 ←
        zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
          (Array.Insts.ZeroizeZeroize 64#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) bytes1
      let s3 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) a4
          { «end» := 32#usize }
      let s4 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s2 s3
      let a5 := to_slice_mut_back s4
      let field_mask_entropy1 := deref_mut_back a5
      let (a6, deref_mut_back1) ←
        zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) leaf_salt_seed
      let (s5, to_slice_mut_back1) ← Aeneas.Std.lift (Array.to_slice_mut a6)
      let s6 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) a4
          { start := 32#usize }
      let s7 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s5 s6
      let a7 := to_slice_mut_back1 s7
      let leaf_salt_seed1 := deref_mut_back1 a7
      let a8 ←
        zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) field_mask_entropy1
      let b ← aspis_prover.state_only_entropy.entropy_nonzero32 a8
      if b
      then
        let a9 ←
          zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
            (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
            U8.Insts.ZeroizeDefaultIsZeroes)) leaf_salt_seed1
        let b1 ← aspis_prover.state_only_entropy.entropy_nonzero32 a9
        if b1
        then
          ok (done (core.result.Result.Ok
            {
              mask_nonce,
              field_mask_entropy := field_mask_entropy1,
              leaf_salt_seed := leaf_salt_seed1
            }))
        else
          let retry1 ← Aeneas.Std.lift (Std.Usize.wrapping_add retry 1#usize)
          ok (cont retry1)
      else
        let retry1 ← Aeneas.Std.lift (Std.Usize.wrapping_add retry 1#usize)
        ok (cont retry1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
          aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.Insts.CoreConvertFromError
          residual
      ok (done r1)

def onFalse (mask_nonce : Array Std.U8 32#usize) (limit : Std.Usize) (retry : Std.Usize) : Result (ControlFlow Std.Usize (core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
    aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError)) := do
    ok (done (core.result.Result.Err
      aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.RepeatedZeroBlock))

/-- Exact first guard of `aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body`.
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (mask_nonce : Array Std.U8 32#usize) (limit : Std.Usize) (retry : Std.Usize) :
  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body (mask_nonce := mask_nonce) (limit := limit) (retry := retry) =
    (if retry < limit then onTrue (mask_nonce := mask_nonce) (limit := limit) (retry := retry) else onFalse (mask_nonce := mask_nonce) (limit := limit) (retry := retry)) := by
  rw [aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body]
  rfl

#print axioms onTrue
#print axioms onFalse
#print axioms first
end R1Z.PV_RE_Guard001
