import NGP_L159
import NGR_HistoryPersist
import NGS_PersistedCarriers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIN_Cuts
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_NativeConsolidation

/-- Deterministic export of named producer values; never an existential Cuts.
Native provenance of f/s/emission/read is retained at the consuming theorem. -/
def of_producers (f : FirstCut) (s : SecondCut) (secondEntry : Entry)
    (prepared : CheckpointBytes5Writer.Prepared)
    (accumulator : CheckpointBytes5Writer.Accumulator)
    (domain : NGC_KNE_Caller.WriterDomain prepared accumulator)
    (hp hu hc : CheckpointBytes5Effect.Digest)
    (emitted : NFY_NEU_EmitModel.Statement) (read : NGK_NFO_ReadModel.Accepted) : NGP_L159.Cuts :=
  { proof1 := f.proof, public1 := f.pub, proof2 := s.proof, public2 := s.pub,
    checkpointRead := secondEntry.buffers (secondEntry.handles 6).1,
    saved := NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc,
    emittedStatement := emitted, poolRead := read }

/-- The byte-carrier/collision fork is unchanged when the SAME Pool reply is
attached. This local lemma does not supply a Pool call or a source prefix. -/
theorem carrier_or_collision {O : Type}
    (f : FirstCut) (s : SecondCut) (e2 : Entry)
    (prepared : CheckpointBytes5Writer.Prepared)
    (accumulator : CheckpointBytes5Writer.Accumulator)
    (domain : NGC_KNE_Caller.WriterDomain prepared accumulator)
    (hp hu hc : CheckpointBytes5Effect.Digest)
    (emitted : NFY_NEU_EmitModel.Statement) (read : NGK_NFO_ReadModel.Accepted)
    (Q : Nat) (recorded : AspisV8R19.MemoizedProgramLaw.View
      AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State O)
    (carriers : (MultiproofConeCanonical.bytesOf s.proof.val = MultiproofConeCanonical.bytesOf f.proof.val ∧
      MultiproofConeCanonical.bytesOf s.pub.val = MultiproofConeCanonical.bytesOf f.pub.val) ∨
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965) recorded)
    (poolBytes : read.bytes = (S2K.ResultPayload.bytes emitted).val)
    (poolValue : read.value = S2K.ResultAdmission.value emitted) :
    NGP_L159.Carrier_statement (of_producers f s e2 prepared accumulator domain hp hu hc emitted read) ∨
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965) recorded := by
  rcases carriers with same | bad
  · exact Or.inl ⟨same.1,same.2,poolBytes,poolValue⟩
  · exact Or.inr bad
#print axioms carrier_or_collision
end AspisR1.NIN_Cuts
