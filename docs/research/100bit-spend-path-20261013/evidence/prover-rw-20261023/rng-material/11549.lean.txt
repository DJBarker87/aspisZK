import R1Z.ProverRwRngMaterialCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngMaterialLastAttempt
open Aeneas Aeneas.Std Result ProverRwRngMaterialBody
open aspis_prover.state_only_entropy aspis_prover.state_only_hiding
open aspis_core.state_only_hiding ProverRwRngMaterialControl ProverRwRngMaterialPaths
open ProverRwRngMaterialProducer
variable [TypeLeaves] [LocalLeaves]
open ProverRwRngMaterialCaller

theorem last_sampling_exhausted {P : Type} (policy : Policy P) (public1 : Public) (compiled : Compiled)
    (a : Secrets) (hash : Hash) (s after : Durable) (p advanced : P)
    (bytes : alloc.vec.Vec U8) (digest binding entropy seed : Array U8 32#usize) (encoded : Array U8 81#usize)
    (cells : Cells) (active : Array Bool 1024#usize) (inactive : Usize) (expanderAfter : Expander)
    (callback : policy.call_mut p 7#usize = .ok (.Ok a,advanced))
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
    prover.retry_attempt policy public1 compiled .S2 hash s p 7#usize = .ok (.Err .AttemptsExhausted,after) := by
  rw [selected_sampling_retry policy public1 compiled a hash s after p advanced 7#usize bytes
    digest binding entropy seed encoded cells active inactive expanderAfter (by decide) callback
    public_bytes public_hash encode binding_hash reserved deref hcells hactive nonzero seed_hash hinactive sample]
  exact cap_stop policy public1 compiled hash after advanced (Usize.wrapping_add 7#usize 1#usize) (by
      have hm : 8 % Usize.size = 8 := by simpa using Usize.val_mod_size_eq (8#usize)
      change (8 : Nat) ≤ (Usize.wrapping_add 7#usize 1#usize).val
      simp [Usize.wrapping_add_val_eq,hm])

#print axioms last_sampling_exhausted
end R1Z.ProverRwRngMaterialLastAttempt
