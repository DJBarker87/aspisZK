import VTop_Cuts
import ChildJoin_Checkpoint

set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_Checkpoint
open Aeneas Aeneas.Std Result VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft
open CheckpointBytes5Effect

def digest {Hash : Type} (D : aspis_core.digest.Digest32 Hash) :
    AspisR1Stage2.aspis_core.digest.Digest32 Hash := ⟨D.coremarkerCopyInst,D.digest⟩

def checkpointSlice (saved : alloc.vec.Vec U8) : Slice U8 := saved.deref

/-- Exact checkpoint child source transport. Neither field states a header,
size, caller acceptance, byte persistence or a Required14 conclusion. -/
structure CheckpointSourceJoin (stage : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (reserved : Bool) : Prop where
  writer : ∀ p a proof pub saved, stage.op8 D p a proof pub hash = ok saved →
    ∃ before after, run (digest D) hash
      (CheckpointBytes5Writer.writer (CheckpointBytes3Namespaces.toPrepared p)
        (CheckpointBytes3Namespaces.toAccumulator a) proof pub) before =
          ok (checkpointSlice saved,after)
  reader : ∀ ck proof pub p a,
    stage.op18 D ck proof pub .S2 hash = ok (.Ok (p,a)) →
    AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
      (digest D) ck proof pub .S2 hash = ok (.Ok (p,a))

/-- The original prepared/accumulator provenance obligation, restricted to
writer calls actually reached by this TX1; it is not folded into source identity. -/
def WriterProvenance (stage : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (proof pub : Slice U8) : Prop :=
  ∀ p a saved, stage.op8 D p a proof pub hash = ok saved →
    ∃ pm am, CheckpointBytes5Join.S1S7S8StateProvenance
      (CheckpointBytes3Namespaces.toPrepared p) (CheckpointBytes3Namespaces.toAccumulator a) pm am

theorem writer_join (adapter : AdapterRw.Ops) (stage : Ops)
    (H : Bytes → State) (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (reserved : Bool)
    (source : CheckpointSourceJoin stage
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (VTop_Entry.install adapter stage)) () reserved)
    (oracle : CheckpointBytes5Inputs.Oracle
      (digest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (VTop_Entry.install adapter stage))) () H)
    (provenance : WriterProvenance stage
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (VTop_Entry.install adapter stage)) () proof pub) :
    S2W_AuthenticatedInputs.CheckpointWriterConeJoin (VTop_Entry.install adapter stage)
      ChildJoin_Decoder.checkpointHeader H semantic pub proof split := by
  have both : ∀ saved, AdapterRw.first_decoded (VTop_Entry.install adapter stage)
      semantic pub proof split = ok (.Ok saved) →
      ChildJoin_Decoder.checkpointHeader (bytesOf saved.val) =
        some (H (bytesOf proof.val),H (bytesOf pub.val)) ∧ saved.val.length = 1768 := by
    intro saved accepted
    have entry := VTop_Entry.first_accepted adapter stage semantic pub proof split saved accepted
    obtain ⟨p,a,wrote⟩ := VTop_Cuts.writer_reached stage _ () semantic pub proof split none saved entry
    obtain ⟨before,after,success⟩ := source.writer p a proof pub saved wrote
    obtain ⟨pm,am,prov⟩ := provenance p a saved wrote
    exact ChildJoin_Checkpoint.writer_header _ () H oracle _ _ pm am prov proof pub
      (checkpointSlice saved) before after success
  exact ⟨fun saved accepted => (both saved accepted).1,fun saved accepted => (both saved accepted).2⟩

theorem reader_join (adapter : AdapterRw.Ops) (stage : Ops)
    (H : Bytes → State) (pub proof ck : Slice U8) (reserved : Bool)
    (source : CheckpointSourceJoin stage
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (VTop_Entry.install adapter stage)) () reserved)
    (oracle : CheckpointBytes5Inputs.Oracle
      (digest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (VTop_Entry.install adapter stage))) () H) :
    S2W_AuthenticatedInputs.CheckpointReaderConeJoin (VTop_Entry.install adapter stage)
      ChildJoin_Decoder.checkpointHeader H pub proof ck := by
  constructor
  intro accepted
  obtain ⟨p,a,resumed⟩ := VTop_Cuts.resume_reached stage _ () pub proof ck none accepted
  exact ChildJoin_Checkpoint.reader_header reserved _ () H oracle ck proof pub p a
    (source.reader ck proof pub p a resumed)

#print axioms writer_join
#print axioms reader_join
end AspisR1.VTop_Checkpoint
end
