import PV_STX_Account
set_option autoImplicit false
noncomputable section
namespace PV_STX_EntropyCleanup
open Aeneas Aeneas.Std ProverRwFull ControlFlow PV_STX_Code PV_STX_DenoteRules
variable [ExternalTypes]
inductive Request : Type → Type 1 where
  | entropy {X : Type} (op : PV_STX_Entropy.Request X) : Request X
  | drop {Z : Type} (size : Nat) (value : zeroize.Zeroizing Z) : Request Unit
variable [ExternalFuns]
/-- Value erasure ONLY. Native drops are requests and cannot be inferred silent. -/
def fixed : {X : Type} → Request X → Result X
  | _,.entropy op => PV_STX_Entropy.fixed op
  | _,.drop _ _ => .ok ()
def nonzero (bytes : Array U8 32#usize) : Code Request Bool :=
  PV_STX_Map.map (fun op => Request.entropy op) (PV_STX_Entropy.nonzero bytes)
theorem nonzero_erases (bytes : Array U8 32#usize) :
    denote fixed (nonzero bytes) = aspis_prover.state_only_entropy.entropy_nonzero32 bytes := by
  rw [nonzero,PV_STX_Map.denote_map (fun op => Request.entropy op) PV_STX_Entropy.fixed fixed (fun _ => rfl)]
  exact PV_STX_Entropy.nonzero_erases bytes

theorem erases_bind {A B : Type} (code : Code Request A) (next : A → Code Request B)
    (r : Result A) (f : A → Result B)
    (hc : denote fixed code = r) (hk : ∀ a, denote fixed (next a) = f a) :
    denote fixed (code >>= next) = (do let a ← r; f a) := by
  rw [bind_rule,hc]
  congr 1
  funext a
  exact hk a

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
      Code.call (Request.entropy <| PV_STX_Entropy.Request.new (Array.Insts.ZeroizeZeroize 64#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a)
    let (s, as_mut_back) ←
      Code.call (Request.entropy <| PV_STX_Entropy.Request.asMut
      (Array.Insts.CoreConvertAsMutSlice Std.U8 64#usize)
      (Array.Insts.ZeroizeZeroize 64#usize (zeroize.Zeroize.Blanket
      U8.Insts.ZeroizeDefaultIsZeroes)) bytes)
    let (r, s1) ←
      Code.call (Request.entropy <| PV_STX_Entropy.Request.fill s)
    let cf ←
      Code.result (core.result.Result.Insts.CoreOpsTry.branch r)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let bytes1 ← Code.call (Request.entropy <| PV_STX_Entropy.Request.restore 9 as_mut_back s1)
      let a1 := Array.repeat 32#usize 0#u8
      let field_mask_entropy ←
        Code.call (Request.entropy <| PV_STX_Entropy.Request.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a1)
      let a2 := Array.repeat 32#usize 0#u8
      let leaf_salt_seed ←
        Code.call (Request.entropy <| PV_STX_Entropy.Request.new (Array.Insts.ZeroizeZeroize 32#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a2)
      let (a3, deref_mut_back) ←
        Code.call (Request.entropy <| PV_STX_Entropy.Request.derefMut
        (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) field_mask_entropy)
      let (s2, to_slice_mut_back) ←
        Code.result (Aeneas.Std.lift (Array.to_slice_mut a3))
      let a4 ←
        Code.call (Request.entropy <| PV_STX_Entropy.Request.deref
        (Array.Insts.ZeroizeZeroize 64#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) bytes1)
      let s3 ←
        Code.result (core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) a4
        { «end» := 32#usize })
      let s4 ←
        Code.result (core.slice.Slice.copy_from_slice core.marker.CopyU8 s2 s3)
      let a5 ← Code.call (Request.entropy <| PV_STX_Entropy.Request.restore 17 to_slice_mut_back s4)
      let field_mask_entropy1 ← Code.call (Request.entropy <| PV_STX_Entropy.Request.restore 18 deref_mut_back a5)
      let (a6, deref_mut_back1) ←
        Code.call (Request.entropy <| PV_STX_Entropy.Request.derefMut
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
      let a7 ← Code.call (Request.entropy <| PV_STX_Entropy.Request.restore 23 to_slice_mut_back1 s7)
      let leaf_salt_seed1 ← Code.call (Request.entropy <| PV_STX_Entropy.Request.restore 24 deref_mut_back1 a7)
      let a8 ←
        Code.call (Request.entropy <| PV_STX_Entropy.Request.deref
        (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) field_mask_entropy1)
      let b ←
        nonzero a8
      if b
      then
        let a9 ←
          Code.call (Request.entropy <| PV_STX_Entropy.Request.deref
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) leaf_salt_seed1)
        let b1 ←
          nonzero a9
        if b1
        then
          let _ ← Code.call (Request.drop 64 bytes1)
          pure (done (core.result.Result.Ok
            {
              mask_nonce,
              field_mask_entropy := field_mask_entropy1,
              leaf_salt_seed := leaf_salt_seed1
            }))
        else
          let retry1 ←
            Code.result (Aeneas.Std.lift (Std.Usize.wrapping_add retry 1#usize))
          let _ ← Code.call (Request.drop 32 leaf_salt_seed1)
          let _ ← Code.call (Request.drop 32 field_mask_entropy1)
          let _ ← Code.call (Request.drop 64 bytes1)
          pure (cont retry1)
      else
        let retry1 ←
          Code.result (Aeneas.Std.lift (Std.Usize.wrapping_add retry 1#usize))
        let _ ← Code.call (Request.drop 32 leaf_salt_seed1)
        let _ ← Code.call (Request.drop 32 field_mask_entropy1)
        let _ ← Code.call (Request.drop 64 bytes1)
        pure (cont retry1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        Code.result (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
        aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.Insts.CoreConvertFromError
        residual)
      let bytes1 ← Code.call (Request.entropy <| PV_STX_Entropy.Request.restore 9 as_mut_back s1)
      let _ ← Code.call (Request.drop 64 bytes1)
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


theorem body_erases (nonce : Array U8 32#usize) (limit retry : Usize) :
    denote fixed (entropyBody nonce limit retry) =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body nonce limit retry := by
  unfold entropyBody aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
  by_cases h : retry < limit
  · simp only [h,if_true]
    apply erases_bind
    · rfl
    · intro bytes
      apply erases_bind
      · rfl
      · rintro ⟨s,back⟩
        apply erases_bind
        · rfl
        · rintro ⟨r,s1⟩
          apply erases_bind
          · rfl
          · intro cf
            cases cf <;> simp only [bind_rule,call_rule,result_rule,pure_rule,if_rule,
              fixed,PV_STX_Entropy.fixed,nonzero_erases,Aeneas.Std.bind_tc_ok]
            all_goals simp only [Bind.bind,Aeneas.Std.bind]
            all_goals repeat first | rfl | split
  · simp only [h,if_false,pure_rule]

#print axioms erases_bind
#print axioms nonzero_erases
#print axioms body_erases
end PV_STX_EntropyCleanup
