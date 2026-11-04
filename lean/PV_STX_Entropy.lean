import PV_STX_DenoteRules
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_STX_Entropy
open Aeneas Aeneas.Std ProverRwFull ControlFlow
open PV_STX_Code PV_STX_DenoteRules
variable [ExternalTypes]

/-- The actual five opaque call points reached by the entropy source body.
Their arguments, mutable restoration functions, and source errors are retained.
No world reply is supplied at construction time. -/
inductive Request : Type → Type 1 where
  | restore {X Y : Type} (site : Nat) (back : X → Y) (value : X) : Request Y
  | new {Z : Type} (zi : zeroize.Zeroize Z) (value : Z) : Request (zeroize.Zeroizing Z)
  | asMut {T Z : Type} (inst : core.convert.AsMut Z T) (zi : zeroize.Zeroize Z)
      (value : zeroize.Zeroizing Z) : Request (T × (T → zeroize.Zeroizing Z))
  | derefMut {Z : Type} (zi : zeroize.Zeroize Z) (value : zeroize.Zeroizing Z) :
      Request (Z × (Z → zeroize.Zeroizing Z))
  | deref {Z : Type} (zi : zeroize.Zeroize Z) (value : zeroize.Zeroizing Z) : Request Z
  | fill (buffer : Slice U8) : Request ((core.result.Result Unit getrandom.error.Error) × Slice U8)

variable [ExternalFuns]
def fixed : {X : Type} → Request X → Result X
  | _, .restore _ back value => .ok (back value)
  | _, .new zi value => zeroize.Zeroizing.new zi value
  | _, .asMut inst zi value => zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut inst zi value
  | _, .derefMut zi value => zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut zi value
  | _, .deref zi value => zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref zi value
  | _, .fill buffer => getrandom.fill buffer

def nonzeroBody
  (bytes : Array Std.U8 32#usize) (combined : Std.U8) (i : Std.Usize) :
  Code Request (ControlFlow (Std.U8 × Std.Usize) Std.U8)
  := do
  if i < 32#usize
  then
    let i1 ←
      Code.result (Array.index_usize bytes i)
    let combined1 ←
      Code.result (Aeneas.Std.lift (combined ||| i1))
    let i2 ←
      Code.result (Aeneas.Std.lift (Std.Usize.wrapping_add i 1#usize))
    pure (cont (combined1, i2))
  else pure (done combined)

def nonzeroLoop
  (bytes : Array Std.U8 32#usize) (combined : Std.U8) (i : Std.Usize) :
  Code Request Std.U8
  := do
  Code.loop
    (fun (combined1, i1) =>
      nonzeroBody bytes
      combined1 i1)
    (combined, i)

def nonzero
  (bytes : Array Std.U8 32#usize) : Code Request Bool := do
  let combined ←
    nonzeroLoop bytes 0#u8 0#usize
  pure (combined != 0#u8)

def
  entropyBody
  (mask_nonce : Array Std.U8 32#usize) (limit : Std.Usize) (retry : Std.Usize)
  :
  Code Request (ControlFlow Std.Usize (core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
    aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError))
  := do
  if retry < limit
  then
    let a := Array.repeat 64#usize 0#u8
    let bytes ←
      Code.call (Request.new (Array.Insts.ZeroizeZeroize 64#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a)
    let (s, as_mut_back) ←
      Code.call (Request.asMut
      (Array.Insts.CoreConvertAsMutSlice Std.U8 64#usize)
      (Array.Insts.ZeroizeZeroize 64#usize (zeroize.Zeroize.Blanket
      U8.Insts.ZeroizeDefaultIsZeroes)) bytes)
    let (r, s1) ←
      Code.call (Request.fill s)
    let cf ←
      Code.result (core.result.Result.Insts.CoreOpsTry.branch r)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let bytes1 ← Code.call (Request.restore 9 as_mut_back s1)
      let a1 := Array.repeat 32#usize 0#u8
      let field_mask_entropy ←
        Code.call (Request.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a1)
      let a2 := Array.repeat 32#usize 0#u8
      let leaf_salt_seed ←
        Code.call (Request.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a2)
      let (a3, deref_mut_back) ←
        Code.call (Request.derefMut
        (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) field_mask_entropy)
      let (s2, to_slice_mut_back) ←
        Code.result (Aeneas.Std.lift (Array.to_slice_mut a3))
      let a4 ←
        Code.call (Request.deref
        (Array.Insts.ZeroizeZeroize 64#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) bytes1)
      let s3 ←
        Code.result (core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) a4
        { «end» := 32#usize })
      let s4 ←
        Code.result (core.slice.Slice.copy_from_slice core.marker.CopyU8 s2 s3)
      let a5 ← Code.call (Request.restore 17 to_slice_mut_back s4)
      let field_mask_entropy1 ← Code.call (Request.restore 18 deref_mut_back a5)
      let (a6, deref_mut_back1) ←
        Code.call (Request.derefMut
        (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) leaf_salt_seed)
      let (s5, to_slice_mut_back1) ←
        Code.result (Aeneas.Std.lift (Array.to_slice_mut a6))
      let s6 ←
        Code.result (core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) a4
        { start := 32#usize })
      let s7 ←
        Code.result (core.slice.Slice.copy_from_slice core.marker.CopyU8 s5 s6)
      let a7 ← Code.call (Request.restore 23 to_slice_mut_back1 s7)
      let leaf_salt_seed1 ← Code.call (Request.restore 24 deref_mut_back1 a7)
      let a8 ←
        Code.call (Request.deref
        (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) field_mask_entropy1)
      let b ←
        nonzero a8
      if b
      then
        let a9 ←
          Code.call (Request.deref
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) leaf_salt_seed1)
        let b1 ←
          nonzero a9
        if b1
        then
          pure (done (core.result.Result.Ok
            {
              mask_nonce,
              field_mask_entropy := field_mask_entropy1,
              leaf_salt_seed := leaf_salt_seed1
            }))
        else
          let retry1 ←
            Code.result (Aeneas.Std.lift (Std.Usize.wrapping_add retry 1#usize))
          pure (cont retry1)
      else
        let retry1 ←
          Code.result (Aeneas.Std.lift (Std.Usize.wrapping_add retry 1#usize))
        pure (cont retry1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        Code.result (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
        aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.Insts.CoreConvertFromError
        residual)
      pure (done r1)
  else
    pure (done (core.result.Result.Err
      aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.RepeatedZeroBlock))

def
  entropyLoop
  (mask_nonce : Array Std.U8 32#usize) (limit : Std.Usize) (retry : Std.Usize)
  :
  Code Request (core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
    aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError)
  := do
  Code.loop
    (fun retry1 =>
      entropyBody
      mask_nonce limit retry1)
    retry

def
  generate
  (mask_nonce : Array Std.U8 32#usize) :
  Code Request (core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
    aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError)
  := do
  let b ←
    nonzero mask_nonce
  if b
  then
    entropyLoop
      mask_nonce aspis_prover.state_only_entropy.ENTROPY_RETRY_LIMIT 0#usize
  else
    pure (core.result.Result.Err
      aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.RepeatedZeroBlock)

/-- Symbolic erasure, not a native trace law. These equalities impose NO
fixed-answer condition on an advancing handler. -/
theorem nonzeroBody_erases (bytes : Array U8 32#usize) (combined : U8) (i : Usize) :
    denote fixed (nonzeroBody bytes combined i) =
      aspis_prover.state_only_entropy.entropy_nonzero32_loop.body bytes combined i := by
  simp only [nonzeroBody, aspis_prover.state_only_entropy.entropy_nonzero32_loop.body,
    if_rule, bind_rule, result_rule, pure_rule]

theorem nonzeroLoop_erases (bytes : Array U8 32#usize) (combined : U8) (i : Usize) :
    denote fixed (nonzeroLoop bytes combined i) =
      aspis_prover.state_only_entropy.entropy_nonzero32_loop bytes combined i := by
  simp only [nonzeroLoop, loop_rule, nonzeroBody_erases, aspis_prover.state_only_entropy.entropy_nonzero32_loop]

theorem nonzero_erases (bytes : Array U8 32#usize) :
    denote fixed (nonzero bytes) = aspis_prover.state_only_entropy.entropy_nonzero32 bytes := by
  simp only [nonzero, bind_rule, nonzeroLoop_erases, pure_rule, aspis_prover.state_only_entropy.entropy_nonzero32]

theorem entropyBody_erases (nonce : Array U8 32#usize) (limit retry : Usize) :
    denote fixed (entropyBody nonce limit retry) =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body nonce limit retry := by
  simp only [entropyBody, aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body, if_rule, bind_rule, call_rule, result_rule, pure_rule, cf_rule, pair_rule, fixed, nonzero_erases]

theorem entropyLoop_erases (nonce : Array U8 32#usize) (limit retry : Usize) :
    denote fixed (entropyLoop nonce limit retry) =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop nonce limit retry := by
  simp only [entropyLoop, loop_rule, entropyBody_erases, aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop]

theorem generate_erases (nonce : Array U8 32#usize) :
    denote fixed (generate nonce) =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce nonce := by
  simp only [generate, bind_rule, nonzero_erases, if_rule, entropyLoop_erases, pure_rule, aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce]

#print axioms nonzeroBody_erases
#print axioms nonzeroLoop_erases
#print axioms nonzero_erases
#print axioms entropyBody_erases
#print axioms entropyLoop_erases
#print axioms generate_erases
end PV_STX_Entropy
