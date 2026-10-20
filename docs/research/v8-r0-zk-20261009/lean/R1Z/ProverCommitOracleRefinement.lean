import R1Z.ProverCommitGrammarSource

/-! D92: byte-oracle-parametric callback refinement. This module identifies
callback evaluation with a single arbitrary function of concatenated bytes.
It does not supply the missing source prover/tape or entropy distributions. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.ProverCommitOracleRefinement
open R1Z.ProverCommitStreamSource

abbrev ByteOracle := List UInt8 → Bytes32

def hashOf (oracle : ByteOracle) : Hash :=
  fun slices => ok (oracle (ProverCommitStreamBytes.wireBytes slices))

/-- A cache is a restriction of one oracle. No injectivity or independence
property of that oracle is required for relational equality. -/
def CacheValid {Answer : Type} (oracle : List UInt8 → Answer)
    (cache : List (List UInt8 × Answer)) : Prop :=
  ∀ entry ∈ cache, entry.2 = oracle entry.1

def cached {Answer : Type} (oracle : List UInt8 → Answer)
    (input : List UInt8) : List (List UInt8 × Answer) → Answer
  | [] => oracle input
  | entry :: rest => if entry.1 = input then entry.2 else cached oracle input rest

theorem cached_eq {Answer : Type} (oracle : List UInt8 → Answer)
    (input : List UInt8) (cache : List (List UInt8 × Answer))
    (valid : CacheValid oracle cache) : cached oracle input cache = oracle input := by
  induction cache with
  | nil => rfl
  | cons entry rest ih =>
    simp only [cached]
    split
    next h => simpa only [h] using valid entry (by simp)
    next => exact ih (fun e he => valid e (by simp [he]))

theorem cache_insert {Answer : Type} (oracle : List UInt8 → Answer)
    (input : List UInt8) (cache : List (List UInt8 × Answer))
    (valid : CacheValid oracle cache) :
    CacheValid oracle ((input, oracle input) :: cache) := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · exact valid entry member

/-- Every fresh arbitrary answer extends a finite consistent function. This
is why a shared memoised symbolic oracle suffices without a SHA theorem. -/
theorem arbitrary_fresh_extension {Answer : Type} (oracle : List UInt8 → Answer)
    (input : List UInt8) (answer : Answer) (cache : List (List UInt8 × Answer))
    (valid : CacheValid oracle cache) (fresh : ∀ e ∈ cache, e.1 ≠ input) :
    CacheValid (fun key => if key = input then answer else oracle key)
      ((input, answer) :: cache) := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | member
  · simp
  · simp only [if_neg (fresh entry member)]
    exact valid entry member

theorem mask_block_refines (oracle : ByteOracle) (seed : Bytes32) (counter : U64) :
    AspisR1ProverStreams.state_only_hiding.state_only_mask_expander_block
      (hashOf oracle) seed counter =
      ok (oracle (R1Z.LayoutR1PBin.dExp1 ++ seed.val.map ProverCommitStreamBytes.byte ++
        R1Z.LayoutR1PBin.le64 counter.val)) := by
  rw [mask_block]
  simp only [hashOf, ProverCommitStreamBytes.block_bytes,
    ProverCommitStreamBytes.mask_domain]

theorem source_block_refines (oracle : ByteOracle) (seed : Bytes32) (counter : U64) :
    AspisR1ProverStreams.state_only_entropy.profile21_source_expander_block
      (hashOf oracle) seed counter =
      ok (oracle (R1Z.LayoutR1PBin.dExp2 ++ seed.val.map ProverCommitStreamBytes.byte ++
        R1Z.LayoutR1PBin.le64 counter.val)) := by
  rw [source_block]
  simp only [hashOf, ProverCommitStreamBytes.block_bytes,
    ProverCommitStreamBytes.source_domain]

theorem leaf_refines (oracle : ByteOracle) (tree : Fin 3)
    (value : Slice U8) (salt : Bytes32) :
    AspisR1ProverLeaf.state_only_private_merkle.private_leaf_hash
      (hashOf oracle) (ProverCommitLeafSource.tagOf tree) value salt =
      ok (oracle (AspisR1.SharedBinaryRecordGrammar.leafInput
        (AspisR1.SharedBinaryRecordGrammar.treeTag tree)
        (value.val.map ProverCommitLeafSource.byte)
        (salt.val.map ProverCommitLeafSource.byte))) := by
  rw [ProverCommitLeafSource.leaf_source]
  change ok (oracle (ProverCommitLeafSource.wireBytes
    (ProverCommitLeafSource.leafSlices (ProverCommitLeafSource.tagOf tree) value salt))) = _
  rw [ProverCommitLeafSource.leaf_shared]

/-- Successful salt evaluation under the same oracle used for its binding.
Validation/binding remain named source joins, not assumptions about hashing. -/
theorem salt_refines (oracle : ByteOracle)
    (self : ProverCommitSaltSource.Reserved)
    (context : ProverCommitSaltSource.Context)
    (tag : U8) (index : U32) (binding : Bytes32)
    (valid : AspisR1ProverCommit.aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context self context = ok (.Ok ()))
    (bound : AspisR1ProverCommit.aspis_prover.state_only_entropy.pool_v1_private_attempt_binding
      (hashOf oracle) self.precommit_binding context = ok binding) :
    AspisR1ProverCommit.aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
      self (hashOf oracle) context tag index =
      ok (.Ok (oracle (R1Z.LayoutR1PBin.dLeafSalt ++
        binding.val.map ProverCommitSaltBytes.byte ++
        self.mask_nonce.val.map ProverCommitSaltBytes.byte ++
        [ProverCommitSaltBytes.byte tag] ++ R1Z.TranscriptR1.le32 index.val ++
        self.leaf_salt_seed.val.map ProverCommitSaltBytes.byte))) := by
  rw [ProverCommitSaltSource.salt_source self (hashOf oracle) context tag index binding valid bound]
  change ok (core.result.Result.Ok (oracle (ProverCommitSaltBytes.wireBytes
    (ProverCommitSaltSource.saltSlices binding self.mask_nonce self.leaf_salt_seed tag index)))) = _
  rw [ProverCommitSaltBytes.salt_bytes]

/-- Pointwise byte equality lifts to complete ordered byte/answer lists for
one arbitrary oracle. Multiplicity and order are preserved by List.map. -/
theorem ordered_reads_refine (oracle : ByteOracle)
    (source model : List (List UInt8)) (same : source = model) :
    source.map (fun input => (input, oracle input)) =
      model.map (fun input => (input, oracle input)) := by
  rw [same]

#print axioms cached_eq
#print axioms cache_insert
#print axioms arbitrary_fresh_extension
#print axioms mask_block_refines
#print axioms source_block_refines
#print axioms leaf_refines
#print axioms salt_refines
#print axioms ordered_reads_refine
end R1Z.ProverCommitOracleRefinement
