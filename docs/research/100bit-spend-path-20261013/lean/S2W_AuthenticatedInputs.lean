import S2W_ExtractionBoundary

/-! Fixed-invocation child joins. Checkpoint authentication yields the two
hash comparisons; P2-prime yields the same proof/public buffers. In particular
neither sameStoredProof nor reconstructed-statement identity is a premise. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_AuthenticatedInputs
open Aeneas Aeneas.Std Result
open AspisR1.AdapterRw MultiproofConeCanonical OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
abbrev Header := State × State
abbrev HeaderDecode := Bytes → Option Header
abbrev Public := AdapterRw.LeadInputs.Public

/-- A checkpoint writer CHILD theorem, conditional on its actual successful
invocation. HeaderDecode is the concrete child header parser port, shared with
the reader. The fields concern its serialization, not retained caller sites,
account writes, cross-TX identity, S2 Inputs or S2CallerFacts. -/
structure CheckpointWriterConeJoin (ops : AdapterRw.Ops) (decode : HeaderDecode)
    (H : Bytes → State) (semantic : Public) (pub proof : Slice U8)
    (split : Usize) : Prop where
  header : ∀ checkpoint, AdapterRw.first_decoded ops semantic pub proof split = ok (.Ok checkpoint) →
    decode (bytesOf checkpoint.val) = some (H (bytesOf proof.val), H (bytesOf pub.val))
  size : ∀ checkpoint, AdapterRw.first_decoded ops semantic pub proof split = ok (.Ok checkpoint) →
    checkpoint.val.length = 1768

/-- Reader CHILD: successful verification checks the SAME parsed stored
header against its actual proof/public digest inputs. This is two digest
comparisons, not proof/public equality, account persistence or S2CallerFacts. -/
structure CheckpointReaderConeJoin (ops : AdapterRw.Ops) (decode : HeaderDecode)
    (H : Bytes → State) (pub proof checkpoint : Slice U8) : Prop where
  checkedHeader : ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      pub proof checkpoint () none = ok (.Ok ()) →
    decode (bytesOf checkpoint.val) = some (H (bytesOf proof.val), H (bytesOf pub.val))

/-- Existing runtime P2-prime, indexed to THIS writer/reader pair. -/
structure P2Prime (H : Bytes → State) (proof1 pub1 proof2 pub2 : Slice U8) : Prop where
  binding : R9PoolRuntimeBinding.P2Prime H
    ⟨bytesOf proof1.val,bytesOf pub1.val⟩ ⟨bytesOf proof2.val,bytesOf pub2.val⟩

/-- Existing protected-version history, with no change of its domain. -/
structure CheckpointVersionBinding (saved loaded : Bytes) where
  history : S2X.CheckpointVersionBinding saved loaded

/-- Authentication composition. savedAtWrite and save/load byte identity are
not assumptions: saved is the actual returned vector; protected history binds
its committed version; reader/writer child headers yield digestMatches.
No full-forest reconstruction equality or universal ChildInputRetention. -/
theorem authenticated_inputs (ops : AdapterRw.Ops) (decode : HeaderDecode)
    (H : Bytes → State) (semantic : Public) (pub1 proof1 pub2 proof2 loaded : Slice U8)
    (split : Usize) (saved : alloc.vec.Vec U8)
    (first : AdapterRw.first_decoded ops semantic pub1 proof1 split = ok (.Ok saved))
    (second : ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      pub2 proof2 loaded () none = ok (.Ok ()))
    (writer : CheckpointWriterConeJoin ops decode H semantic pub1 proof1 split)
    (reader : CheckpointReaderConeJoin ops decode H pub2 proof2 loaded)
    (version : CheckpointVersionBinding (bytesOf saved.val) (bytesOf loaded.val))
    (p2prime : P2Prime H proof1 pub1 proof2 pub2) :
    bytesOf proof2.val = bytesOf proof1.val ∧
    bytesOf pub2.val = bytesOf pub1.val ∧
    bytesOf loaded.val = bytesOf saved.val ∧
    (bytesOf saved.val).length = 1768 := by
  have persisted := S2X.checkpoint_persistence _ _ version.history
  have wrote := writer.header saved first
  have read := reader.checkedHeader second
  rw [persisted,wrote] at read
  have pairs := Option.some.inj read
  have matched : R9PoolRuntimeBinding.digestMatches H
      ⟨bytesOf proof1.val,bytesOf pub1.val⟩ ⟨bytesOf proof2.val,bytesOf pub2.val⟩ :=
    ⟨(congrArg Prod.fst pairs).symm,(congrArg Prod.snd pairs).symm⟩
  obtain ⟨proof,pub⟩ := p2prime.binding matched
  refine ⟨proof,pub,persisted,?_⟩
  simpa only [bytesOf,List.length_map] using writer.size saved first

/-- Consume the two authenticated byte identities on the SAME child geometry
ports. All four source-internal obligations are named per-child hypotheses;
there is no additional sameStoredProof or tx1ProofObservation premise. -/
theorem authenticated_geometry (ops : AdapterRw.Ops) (decode : HeaderDecode)
    (H : Bytes → State) (semantic : Public) (pub1 proof1 pub2 proof2 loaded y1 : Slice U8)
    (nodes : Nat → Nat → Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (first : AdapterRw.first_decoded ops semantic pub1 proof1 split = ok (.Ok saved))
    (second : ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      pub2 proof2 loaded () none = ok (.Ok ()))
    (writer : CheckpointWriterConeJoin ops decode H semantic pub1 proof1 split)
    (reader : CheckpointReaderConeJoin ops decode H pub2 proof2 loaded)
    (version : CheckpointVersionBinding (bytesOf saved.val) (bytesOf loaded.val))
    (p2prime : P2Prime H proof1 pub1 proof2 pub2)
    (entry : S2W_ChildJoins.FirstEntryVerifierConeJoin proof1)
    (multiproof : S2W_ChildJoins.MultiproofConeJoin proof1 proof2 nodes)
    (scan : S2W_ChildJoins.S8StageConeJoin proof1 y1) :
    bytesOf proof2.val = bytesOf proof1.val ∧
    bytesOf pub2.val = bytesOf pub1.val ∧
    bytesOf loaded.val = bytesOf saved.val ∧
    (bytesOf saved.val).length = 1768 ∧
    ∃ tr p, OraclePortStoredParserC4.parseReached (bytesOf proof1.val) tr = some p ∧
      (∀ b k, b < 2 → k < 3 → bytesOf (nodes b k).val =
        slice p.wire (OraclePortSelectedDraft.slotStart (3*b+k))
          (32*OraclePortSelectedDraft.capacity (3*b+k))) ∧
      y1 = S8JoinFrozenScan.segment proof1 7031 464 ∧
      S8OwnedP6.check_values_owned y1 = ok (.Ok ()) := by
  obtain ⟨proof,pub,cp,size⟩ := authenticated_inputs ops decode H semantic pub1 proof1 pub2 proof2
    loaded split saved first second writer reader version p2prime
  exact ⟨proof,pub,cp,size,S2W_ChildJoins.internal_geometry proof1 proof2 y1 nodes
    entry multiproof scan proof⟩

#print axioms authenticated_inputs
#print axioms authenticated_geometry
#print CheckpointWriterConeJoin
#print CheckpointReaderConeJoin
#print P2Prime
#print CheckpointVersionBinding
end AspisR1.S2W_AuthenticatedInputs
end
