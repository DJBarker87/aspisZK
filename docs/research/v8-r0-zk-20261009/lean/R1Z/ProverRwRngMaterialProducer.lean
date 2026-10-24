import R1Z.ProverRwRngMaterialPaths
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngMaterialProducer
open Aeneas Aeneas.Std Result ProverRwRngMaterialBody
open aspis_prover.state_only_entropy aspis_prover.state_only_hiding
open aspis_core.state_only_hiding ProverRwRngMaterialControl ProverRwRngMaterialPaths
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

def statusFor (e : BuildError) : verifier.Error :=
  match e with | .MaskSampleExhausted => .Rejected | _ => .Semantic

theorem mask_error_exact (e : BuildError) :
    prover.mask_error e = .ok (statusFor e) := by
  cases e <;> simp [statusFor,prover.mask_error,
    StateOnlyMaskBuildError.Insts.CoreCmpPartialEqStateOnlyMaskBuildError.eq,StateOnlyMaskBuildError.read_discriminant]

theorem body_reservation_error {S : Type} (store : Store S)
    (public1 : Public) (compiled : Compiled) (variant : transport.Variant)
    (a : Secrets) (hash : Hash) (binding : Array U8 32#usize) (c : Context)
    (s after : S) (e : BuildError)
    (reservation : reserveBuild store a hash binding c s = .ok (.Err e,after)) :
    prover.prove_masked_with_attempt store public1 compiled variant hash c binding a s =
      .ok (.Err (statusFor e),after) := by
  unfold prover.prove_masked_with_attempt
  simp only [reservation,bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.map_err,
    BuiltinFnOnce,mask_error_exact]
  cases e <;> rfl

theorem reserve_material_error {S : Type} (store : Store S)
    (a : Secrets) (hash : Hash) (binding : Array U8 32#usize) (c : Context)
    (s after : S) (entropy : Array U8 32#usize) (ack : PreReservedNonce) (e : BuildError)
    (layout : LayoutOk a c)
    (reserved : store.reserve s c.statement_digest c.mask_nonce = .ok (true,after))
    (deref : derefEntropy a = .ok entropy)
    (built : material hash binding c entropy = .ok (.Err e,ack)) :
    reserveBuild store a hash binding c s = .ok (.Err e,after) := by
  rcases layout with ⟨nonce,mask,factor⟩
  have compare : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      c.mask_nonce a.mask_nonce = .ok false := by rw [nonce,array_ne_self]
  unfold reserveBuild StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
  simp only [derefEntropy] at deref
  simp only [material,freshAck] at built
  simp [compare,mask,factor,reserved,deref,built,core.result.Result.Insts.CoreOpsTry.branch]
  rfl

theorem selected_reservation_error (public1 : Public) (compiled : Compiled)
    (a : Secrets) (hash : Hash) (s after : Durable) (bytes : alloc.vec.Vec U8)
    (digest binding : Array U8 32#usize) (encoded : Array U8 81#usize)
    (public_bytes : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes public1 =
      .ok (.Ok bytes))
    (public_hash : hash (publicHashInput bytes) = .ok digest)
    (encode : StateOnlyHidingContext.encode (contextFor digest a.mask_nonce) = .ok encoded)
    (binding_hash : hash (bindingInput bytes encoded) = .ok binding)
    (e : BuildError)
    (reservation : reserveBuild durableStore a hash binding (contextFor digest a.mask_nonce) s = .ok (.Err e,after)) :
    prover.prove_masked_attempt public1 compiled .S2 hash a s =
      .ok (.Err (statusFor e),after) := by
  have body := body_reservation_error durableStore public1 compiled .S2 a hash binding
    (contextFor digest a.mask_nonce) s after e reservation
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

/-- Selected secure producer, actual acknowledgment and actual zero-entropy
branch. The outer reservation is retained; no buildMaterial reply is assumed. -/
theorem selected_zero_entropy (public1 : Public) (compiled : Compiled)
    (a : Secrets) (hash : Hash) (s after : Durable) (bytes : alloc.vec.Vec U8)
    (digest binding : Array U8 32#usize) (encoded : Array U8 81#usize)
    (cells : Cells) (active : Array Bool 1024#usize)
    (public_bytes : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes public1 = .ok (.Ok bytes))
    (public_hash : hash (publicHashInput bytes) = .ok digest)
    (encode : StateOnlyHidingContext.encode (contextFor digest a.mask_nonce) = .ok encoded)
    (binding_hash : hash (bindingInput bytes encoded) = .ok binding)
    (reserved : durableStore.reserve s digest a.mask_nonce = .ok (true,after))
    (deref : derefEntropy a = .ok (Array.repeat 32#usize 0#u8))
    (hcells : cellsReply = .ok (.Ok cells)) (hactive : activeReply = .ok (.Ok active)) :
    prover.prove_masked_attempt public1 compiled .S2 hash a s = .ok (.Err verifier.Error.Semantic,after) := by
  have built := material_zero_consumes hash binding (contextFor digest a.mask_nonce) cells active rfl rfl hcells hactive
  have reservation := reserve_material_error durableStore a hash binding (contextFor digest a.mask_nonce)
    s after _ _ .ZeroPrivateEntropy ⟨rfl,rfl,rfl⟩ reserved deref built
  exact selected_reservation_error public1 compiled a hash s after bytes digest binding encoded
    public_bytes public_hash encode binding_hash .ZeroPrivateEntropy reservation

/-- Ordered sampling-error path through actual selected source control.
The first sampler remains a named unproved component with its precise state
reply. Specializing e=MaskSampleExhausted gives Rejected, other errors Semantic. -/
theorem selected_sampling_failure (public1 : Public) (compiled : Compiled)
    (a : Secrets) (hash : Hash) (s after : Durable) (bytes : alloc.vec.Vec U8)
    (digest binding entropy seed : Array U8 32#usize) (encoded : Array U8 81#usize)
    (cells : Cells) (active : Array Bool 1024#usize) (inactive : Usize)
    (advanced : Expander) (e : BuildError)
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
    (sample : sample_mask_cells (initial hash seed) (Slice.len (alloc.vec.Vec.deref cells)) = .ok (.Err e,advanced)) :
    prover.prove_masked_attempt public1 compiled .S2 hash a s =
      .ok (.Err (statusFor e),after) := by
  have built : material hash binding (contextFor digest a.mask_nonce) entropy =
      .ok (.Err e,usedAck (contextFor digest a.mask_nonce)) := by
    rw [material_reaches_layout hash binding entropy (contextFor digest a.mask_nonce) cells active rfl rfl hcells hactive]
    exact layout_sample_error hash binding entropy seed _ encoded _ active inactive advanced e
      nonzero encode seed_hash hinactive sample
  have reservation := reserve_material_error durableStore a hash binding (contextFor digest a.mask_nonce)
    s after entropy _ e ⟨rfl,rfl,rfl⟩ reserved deref built
  exact selected_reservation_error public1 compiled a hash s after bytes digest binding encoded
    public_bytes public_hash encode binding_hash e reservation

#print axioms mask_error_exact
#print axioms body_reservation_error
#print axioms reserve_material_error
#print axioms selected_reservation_error
#print axioms selected_zero_entropy
#print axioms selected_sampling_failure
end R1Z.ProverRwRngMaterialProducer
