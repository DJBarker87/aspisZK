import R1Z.ProverRwRngMaterialProducer
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngMaterialCaller
open Aeneas Aeneas.Std Result ProverRwRngMaterialBody
open aspis_prover.state_only_entropy aspis_prover.state_only_hiding
open aspis_core.state_only_hiding ProverRwRngMaterialControl ProverRwRngMaterialPaths
open ProverRwRngMaterialProducer
variable [TypeLeaves] [LocalLeaves]
abbrev Policy (P : Type) := core.ops.function.FnMut P Usize (core.result.Result Secrets verifier.Error)

theorem selected_entry {P : Type} (policy : Policy P) (public1 : Public) (compiled : Compiled)
    (hash : Hash) (store : Durable) (p : P) :
    prover.prove_masked_retrying_with policy public1 compiled .S2 hash store p =
      prover.retry_attempt policy public1 compiled .S2 hash store p 0#usize := by
  simp [prover.prove_masked_retrying_with,core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,transport.Variant.Insts.CoreCmpPartialEqVariant,
    transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant]

theorem cap_stop {P : Type} (policy : Policy P) (public1 : Public) (compiled : Compiled)
    (hash : Hash) (store : Durable) (p : P) (k : Usize) (full : k ≥ 8#usize) :
    prover.retry_attempt policy public1 compiled .S2 hash store p k =
      .ok (.Err verifier.Error.AttemptsExhausted,store) := by
  conv_lhs => rw [prover.retry_attempt]
  simp [prover.ATTEMPT_CAP,full]

theorem callback_error {P : Type} (policy : Policy P) (public1 : Public) (compiled : Compiled)
    (hash : Hash) (store : Durable) (p advanced : P) (k : Usize) (e : verifier.Error)
    (below : k < 8#usize) (callback : policy.call_mut p k = .ok (.Err e,advanced)) :
    prover.retry_attempt policy public1 compiled .S2 hash store p k = .ok (.Err e,store) := by
  conv_lhs => rw [prover.retry_attempt]
  simp [prover.ATTEMPT_CAP,not_le_of_gt below,callback,core.result.Result.Insts.CoreOpsTry.branch]
  rfl

/-- Consumer lemma for the exact concrete source call, not an arbitrary Body
instance. The concrete material path below discharges its body premise. -/
theorem body_fatal {P : Type} (policy : Policy P) (public1 : Public) (compiled : Compiled)
    (hash : Hash) (store after : Durable) (p advanced : P) (k : Usize) (a : Secrets)
    (e : verifier.Error) (fatal : e ≠ .Rejected) (below : k < 8#usize)
    (callback : policy.call_mut p k = .ok (.Ok a,advanced))
    (body : prover.prove_masked_attempt public1 compiled .S2 hash a store = .ok (.Err e,after)) :
    prover.retry_attempt policy public1 compiled .S2 hash store p k = .ok (.Err e,after) := by
  conv_lhs => rw [prover.retry_attempt]
  simp only [prover.ATTEMPT_CAP,not_le_of_gt below,if_false,callback,bind_tc_ok,
    Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,body]
  cases e <;> try rfl
  exact False.elim (fatal rfl)

theorem body_rejected {P : Type} (policy : Policy P) (public1 : Public) (compiled : Compiled)
    (hash : Hash) (store after : Durable) (p advanced : P) (k : Usize) (a : Secrets)
    (below : k < 8#usize) (callback : policy.call_mut p k = .ok (.Ok a,advanced))
    (body : prover.prove_masked_attempt public1 compiled .S2 hash a store = .ok (.Err .Rejected,after)) :
    prover.retry_attempt policy public1 compiled .S2 hash store p k =
      prover.retry_attempt policy public1 compiled .S2 hash after advanced
        (Usize.wrapping_add k 1#usize) := by
  conv_lhs => rw [prover.retry_attempt]
  simp [prover.ATTEMPT_CAP,not_le_of_gt below,callback,body,core.result.Result.Insts.CoreOpsTry.branch,lift]

/-- This structural consumer retains the concrete native audit value. It
still assumes the actual body succeeded; it is not a successful-body proof. -/
theorem body_success {P : Type} (policy : Policy P) (public1 : Public) (compiled : Compiled)
    (hash : Hash) (store after : Durable) (p advanced : P) (k : Usize) (a : Secrets)
    (proof : alloc.vec.Vec U8) (audit : prover.MaskedFixtureAudit)
    (below : k < 8#usize) (callback : policy.call_mut p k = .ok (.Ok a,advanced))
    (body : prover.prove_masked_attempt public1 compiled .S2 hash a store = .ok (.Ok (proof,audit),after)) :
    prover.retry_attempt policy public1 compiled .S2 hash store p k =
      .ok (.Ok ⟨proof,audit,Usize.wrapping_add k 1#usize⟩,after) := by
  conv_lhs => rw [prover.retry_attempt]
  simp [prover.ATTEMPT_CAP,not_le_of_gt below,callback,body,core.result.Result.Insts.CoreOpsTry.branch,lift]

theorem selected_zero_fatal {P : Type} (policy : Policy P) (public1 : Public) (compiled : Compiled)
    (a : Secrets) (hash : Hash) (s after : Durable) (p advanced : P) (k : Usize)
    (bytes : alloc.vec.Vec U8) (digest binding : Array U8 32#usize) (encoded : Array U8 81#usize)
    (cells : Cells) (active : Array Bool 1024#usize)
    (below : k < 8#usize) (callback : policy.call_mut p k = .ok (.Ok a,advanced))
    (public_bytes : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes public1 = .ok (.Ok bytes))
    (public_hash : hash (publicHashInput bytes) = .ok digest)
    (encode : StateOnlyHidingContext.encode (contextFor digest a.mask_nonce) = .ok encoded)
    (binding_hash : hash (bindingInput bytes encoded) = .ok binding)
    (reserved : durableStore.reserve s digest a.mask_nonce = .ok (true,after))
    (deref : derefEntropy a = .ok (Array.repeat 32#usize 0#u8))
    (hcells : cellsReply = .ok (.Ok cells)) (hactive : activeReply = .ok (.Ok active)) :
    prover.retry_attempt policy public1 compiled .S2 hash s p k = .ok (.Err .Semantic,after) := by
  exact body_fatal policy public1 compiled hash s after p advanced k a .Semantic
    (by intro h; cases h) below callback
    (selected_zero_entropy public1 compiled a hash s after bytes digest binding encoded cells active
      public_bytes public_hash encode binding_hash reserved deref hcells hactive)

theorem selected_sampling_retry {P : Type} (policy : Policy P) (public1 : Public) (compiled : Compiled)
    (a : Secrets) (hash : Hash) (s after : Durable) (p advanced : P) (k : Usize)
    (bytes : alloc.vec.Vec U8) (digest binding entropy seed : Array U8 32#usize) (encoded : Array U8 81#usize)
    (cells : Cells) (active : Array Bool 1024#usize) (inactive : Usize) (expanderAfter : Expander)
    (below : k < 8#usize) (callback : policy.call_mut p k = .ok (.Ok a,advanced))
    (public_bytes : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes public1 = .ok (.Ok bytes))
    (public_hash : hash (publicHashInput bytes) = .ok digest)
    (encode : StateOnlyHidingContext.encode (contextFor digest a.mask_nonce) = .ok encoded)
    (binding_hash : hash (bindingInput bytes encoded) = .ok binding)
    (reserved : durableStore.reserve s digest a.mask_nonce = .ok (true,after))
    (deref : derefEntropy a = .ok entropy)
    (hcells : cellsReply = .ok (.Ok cells)) (hactive : activeReply = .ok (.Ok active))
    (nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 entropy
      (Array.repeat 32#usize 0#u8) = .ok false)
    (seed_hash : hash (seedInput binding encoded entropy) = .ok seed)
    (hinactive : first_inactive_row active = .ok inactive)
    (sample : sample_mask_cells (initial hash seed) (Slice.len (alloc.vec.Vec.deref cells)) =
      .ok (.Err .MaskSampleExhausted,expanderAfter)) :
    prover.retry_attempt policy public1 compiled .S2 hash s p k =
      prover.retry_attempt policy public1 compiled .S2 hash after advanced
        (Usize.wrapping_add k 1#usize) := by
  exact body_rejected policy public1 compiled hash s after p advanced k a below callback
    (selected_sampling_failure public1 compiled a hash s after bytes digest binding entropy seed encoded cells active
      inactive expanderAfter .MaskSampleExhausted public_bytes public_hash encode binding_hash reserved deref
      hcells hactive nonzero seed_hash hinactive sample)

#print axioms selected_entry
#print axioms cap_stop
#print axioms callback_error
#print axioms body_fatal
#print axioms body_rejected
#print axioms body_success
#print axioms selected_zero_fatal
#print axioms selected_sampling_retry
end R1Z.ProverRwRngMaterialCaller
