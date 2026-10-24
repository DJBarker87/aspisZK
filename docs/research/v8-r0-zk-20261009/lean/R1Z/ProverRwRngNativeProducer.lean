import R1Z.ProverRwRngNativeBuildControl
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngNativeProducer
open Aeneas Aeneas.Std Result ProverRwRngNativeBody
open aspis_prover.state_only_entropy aspis_prover.state_only_hiding
open aspis_core.state_only_hiding ProverRwRngNativeReserve ProverRwRngNativeBuildControl
variable [TypeLeaves] [LocalLeaves]
abbrev Durable := DurableStateOnlyMaskNonceStore
abbrev durableStore := DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Compiled := aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1

def contextFor (digest nonce : Array U8 32#usize) : Context :=
  ⟨digest,nonce,PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1,
    PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1⟩

def privateDomain : Array U8 30#usize := Array.make 30#usize [
  85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,
  49#u8,58#u8,80#u8,51#u8,58#u8,80#u8,82#u8,73#u8,86#u8,65#u8,
  84#u8,69#u8,45#u8,65#u8,84#u8,84#u8,69#u8,77#u8,80#u8,84#u8]

def publicHashInput (bytes : alloc.vec.Vec U8) : Slice (Slice U8) :=
  (Array.make 1#usize [alloc.vec.Vec.deref bytes]).to_slice

def bindingInput (bytes : alloc.vec.Vec U8) (encoded : Array U8 81#usize) : Slice (Slice U8) :=
  (Array.make 4#usize [privateDomain.to_slice,alloc.vec.Vec.deref bytes,
    (Array.make 1#usize [2#u8]).to_slice,encoded.to_slice]).to_slice

theorem durable_duplicate (s after : Durable) (digest nonce : Array U8 32#usize)
    (fs : DurableStateOnlyMaskNonceStore.reserve_fallible s digest nonce = .ok (.Ok false,after)) :
    durableStore.reserve s digest nonce = .ok (false,after) := by
  simp only [durableStore,DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve,
    fs,bind_tc_ok,Aeneas.Std.uncurry]

theorem durable_failure (s after : Durable) (digest nonce : Array U8 32#usize)
    (error : ProverRwRngNativeBody.std.io.error.Error) (kind : core.io.error.ErrorKind)
    (fs : DurableStateOnlyMaskNonceStore.reserve_fallible s digest nonce = .ok (.Err error,after))
    (classify : ProverRwRngNativeBody.std.io.error.Error.kind error = .ok kind) :
    durableStore.reserve s digest nonce = .ok (false,{after with last_error := some kind}) := by
  simp only [durableStore,DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve,
    fs,classify,bind_tc_ok,Aeneas.Std.uncurry]

theorem selected_reservation_false (public1 : Public) (compiled : Compiled)
    (a : Secrets) (hash : Hash) (s after : Durable) (bytes : alloc.vec.Vec U8)
    (digest binding : Array U8 32#usize) (encoded : Array U8 81#usize)
    (public_bytes : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes public1 =
      .ok (.Ok bytes))
    (public_hash : hash (publicHashInput bytes) = .ok digest)
    (encode : StateOnlyHidingContext.encode (contextFor digest a.mask_nonce) = .ok encoded)
    (binding_hash : hash (bindingInput bytes encoded) = .ok binding)
    (reservation : durableStore.reserve s digest a.mask_nonce = .ok (false,after)) :
    prover.prove_masked_attempt public1 compiled .S2 hash a s =
      .ok (.Err verifier.Error.Semantic,after) := by
  have body := duplicate_fatal durableStore public1 compiled .S2 a hash binding
    (contextFor digest a.mask_nonce) s after (by exact ⟨rfl,rfl,rfl⟩) reservation
  unfold prover.prove_masked_attempt
  simp only [public_bytes,core.result.Result.map_err,bind_tc_ok,Aeneas.Std.uncurry]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  simp only [lift,publicHashInput] at public_hash ⊢
  simp only [public_hash,bind_tc_ok,StateOnlyAttemptSecrets.impl.mask_nonce,
    StateOnlyHidingContext.pool_v1_pair_forest_v1]
  change (do
    let encoded ← StateOnlyHidingContext.encode (contextFor digest a.mask_nonce)
    let binding ← hash (bindingInput bytes encoded)
    prover.prove_masked_with_attempt durableStore public1 compiled .S2 hash
      (contextFor digest a.mask_nonce) binding a s) = _
  simp only [encode,bind_tc_ok,binding_hash]
  exact body

theorem selected_duplicate_fatal (public1 : Public) (compiled : Compiled)
    (a : Secrets) (hash : Hash) (s after : Durable) (bytes : alloc.vec.Vec U8)
    (digest binding : Array U8 32#usize) (encoded : Array U8 81#usize)
    (public_bytes : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes public1 =
      .ok (.Ok bytes))
    (public_hash : hash (publicHashInput bytes) = .ok digest)
    (encode : StateOnlyHidingContext.encode (contextFor digest a.mask_nonce) = .ok encoded)
    (binding_hash : hash (bindingInput bytes encoded) = .ok binding)
    (fs : DurableStateOnlyMaskNonceStore.reserve_fallible s digest a.mask_nonce = .ok (.Ok false,after)) :
    prover.prove_masked_attempt public1 compiled .S2 hash a s =
      .ok (.Err verifier.Error.Semantic,after) := by
  exact selected_reservation_false public1 compiled a hash s after bytes digest binding encoded
    public_bytes public_hash encode binding_hash (durable_duplicate s after digest a.mask_nonce fs)

theorem selected_io_failure (public1 : Public) (compiled : Compiled)
    (a : Secrets) (hash : Hash) (s after : Durable) (bytes : alloc.vec.Vec U8)
    (digest binding : Array U8 32#usize) (encoded : Array U8 81#usize)
    (error : ProverRwRngNativeBody.std.io.error.Error) (kind : core.io.error.ErrorKind)
    (public_bytes : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes public1 =
      .ok (.Ok bytes))
    (public_hash : hash (publicHashInput bytes) = .ok digest)
    (encode : StateOnlyHidingContext.encode (contextFor digest a.mask_nonce) = .ok encoded)
    (binding_hash : hash (bindingInput bytes encoded) = .ok binding)
    (fs : DurableStateOnlyMaskNonceStore.reserve_fallible s digest a.mask_nonce = .ok (.Err error,after))
    (classify : ProverRwRngNativeBody.std.io.error.Error.kind error = .ok kind) :
    prover.prove_masked_attempt public1 compiled .S2 hash a s =
      .ok (.Err verifier.Error.Semantic,{after with last_error := some kind}) := by
  exact selected_reservation_false public1 compiled a hash s _ bytes digest binding encoded
    public_bytes public_hash encode binding_hash
    (durable_failure s after digest a.mask_nonce error kind fs classify)

#print axioms durable_duplicate
#print axioms durable_failure
#print axioms selected_reservation_false
#print axioms selected_duplicate_fatal
#print axioms selected_io_failure
end R1Z.ProverRwRngNativeProducer
