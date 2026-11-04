import PV_EVH_World
set_option autoImplicit false
noncomputable section
namespace PV_EVH_Entropy
open Aeneas Aeneas.Std ProverRwFull ControlFlow
open PV_EVH_World
open PV_RJ4IDB (NativeEvent)
variable [ExternalTypes] [ExternalFuns]

abbrev FillReply := Result ((core.result.Result Unit getrandom.error.Error) × Slice U8)
abbrev EntropyAnswers := Nat → Slice U8 → FillReply

def ascii (s : String) : PV_RJ4IDB.Bytes :=
  s.toList.map (fun c => UInt8.ofNat c.toNat)

def draw (answers : EntropyAnswers) (buffer : Slice U8) : M
    ((core.result.Result Unit getrandom.error.Error) × Slice U8) := fun w =>
  let r := answers w.entropyCursor buffer
  let next := {w with entropyCursor := w.entropyCursor + 1}
  let request := NativeEvent.side (ascii "entropy-request") (ascii (toString w.entropyCursor))
  match r with
  | .div => ⟨.div,next,[request]⟩
  | _ => ⟨r,next,[request,
      .side (ascii "entropy-delivery") (ascii (toString w.entropyCursor))]⟩

theorem draw_fixed (answers : EntropyAnswers)
    (h : ∀ n s, answers n s = getrandom.fill s) (buffer : Slice U8) :
    FixedView (draw answers buffer) (getrandom.fill buffer) :=
  by
    intro w
    cases hr : answers w.entropyCursor buffer <;>
      simpa only [draw,hr] using h w.entropyCursor buffer

/- Exact emitted body, only monad lift / entropy primitive interpretation.
Every other helper remains a fixed Result call: whole-prover event credit is
NOT claimed. The structural diff and original hash are recorded separately. -/
def afterDraw (mask_nonce : Array U8 32#usize) (retry : Usize)
    (as_mut_back : Slice U8 → zeroize.Zeroizing (Array U8 64#usize))
    (r : core.result.Result Unit getrandom.error.Error) (s1 : Slice U8) : Result (ControlFlow Usize (core.result.Result aspis_prover.state_only_entropy.StateOnlyAttemptSecrets aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError)) := do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let bytes1 := as_mut_back s1
    let a1 := Array.repeat 32#usize 0#u8
    let field_mask_entropy ← zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a1
    let a2 := Array.repeat 32#usize 0#u8
    let leaf_salt_seed ← zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a2
    let (a3, deref_mut_back) ← zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut
        (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) field_mask_entropy
    let (s2, to_slice_mut_back) ← Aeneas.Std.lift (Array.to_slice_mut a3)
    let a4 ← zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 64#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) bytes1
    let s3 ← core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) a4
        { «end» := 32#usize }
    let s4 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s2 s3
    let a5 := to_slice_mut_back s4
    let field_mask_entropy1 := deref_mut_back a5
    let (a6, deref_mut_back1) ← zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut
        (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) leaf_salt_seed
    let (s5, to_slice_mut_back1) ← Aeneas.Std.lift (Array.to_slice_mut a6)
    let s6 ← core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) a4
        { start := 32#usize }
    let s7 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s5 s6
    let a7 := to_slice_mut_back1 s7
    let leaf_salt_seed1 := deref_mut_back1 a7
    let a8 ← zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) field_mask_entropy1
    let b ← aspis_prover.state_only_entropy.entropy_nonzero32 a8
    if b then
      let a9 ← zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) leaf_salt_seed1
      let b1 ← aspis_prover.state_only_entropy.entropy_nonzero32 a9
      if b1 then
        Result.ok (done (core.result.Result.Ok
          {
          mask_nonce,
          field_mask_entropy := field_mask_entropy1,
          leaf_salt_seed := leaf_salt_seed1
          }))
      else
        let retry1 ← Aeneas.Std.lift (Std.Usize.wrapping_add retry 1#usize)
        Result.ok (cont retry1)
    else
      let retry1 ← Aeneas.Std.lift (Std.Usize.wrapping_add retry 1#usize)
      Result.ok (cont retry1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
        aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.Insts.CoreConvertFromError
        residual
    Result.ok (done r1)

def entropyBody (answers : EntropyAnswers)
  (mask_nonce : Array Std.U8 32#usize) (limit : Std.Usize) (retry : Std.Usize)
  :
  M (ControlFlow Std.Usize (core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
    aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError))
  := do
  if retry < limit then
    let a := Array.repeat 64#usize 0#u8
    let bytes ← PV_EVH_World.lift (zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 64#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a)
    let (s, as_mut_back) ← PV_EVH_World.lift (zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut
        (Array.Insts.CoreConvertAsMutSlice Std.U8 64#usize)
        (Array.Insts.ZeroizeZeroize 64#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) bytes)
    let (r, s1) ← draw answers s
    PV_EVH_World.lift (afterDraw mask_nonce retry as_mut_back r s1)
  else
    pure (done (core.result.Result.Err
      aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.RepeatedZeroBlock))

/-- Complete Result equality for the actual emitted iteration on the fixed
answer view. afterDraw is exact source syntax, not an arbitrary callback. Its
other effects are NOT interpreted by this entropy-only subprogram. -/
theorem entropyBody_fixed (answers : EntropyAnswers)
    (h : ∀ n s, answers n s = getrandom.fill s)
    (mask_nonce : Array U8 32#usize) (limit retry : Usize) :
    FixedView (entropyBody answers mask_nonce limit retry)
      (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body mask_nonce limit retry) := by
  unfold entropyBody aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
  by_cases condition : retry < limit
  · simp only [condition,if_true]
    let a := Array.repeat 64#usize 0#u8
    try dsimp only
    try dsimp only
    apply fixed_bind
    ·
      exact fixed_lift _
    · intro bytes
      try dsimp only
      apply fixed_bind
      ·
        exact fixed_lift _
      · rintro ⟨s, as_mut_back⟩
        try dsimp only
        apply fixed_bind
        ·
          exact draw_fixed answers h _
        · rintro ⟨r, s1⟩
          exact fixed_lift _
  · simp only [condition,if_false]
    exact fixed_lift _

#print axioms entropyBody_fixed

#print axioms draw_fixed
end PV_EVH_Entropy
