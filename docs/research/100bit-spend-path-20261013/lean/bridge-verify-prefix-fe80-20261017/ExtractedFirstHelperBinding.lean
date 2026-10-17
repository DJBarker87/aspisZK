import ExtractedVerifyPrefixReachability
import ExtractedFirstCallerReachability

/-! Full emitted first → actual tx1 → actual verify prefix → actual helper.
The first SDK observer/error interpretation and post-begin/tx1 tail boundaries
remain explicit; no child success, decoder result, public equality or serializer
success is assumed. Custody and completed transcript agreement are separate. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.FirstHelperBinding

/-- The exact constructor-by-constructor nominal observer carrier transport. -/
def phaseToFirst : verifier.Phase → FirstCaller.Phase
  | .Parsed => .Parsed
  | .Semantic => .Semantic
  | .SemanticPart i => .SemanticPart i
  | .Prepare => .Prepare
  | .CheckpointRead => .CheckpointRead
  | .Merkle i => .Merkle i
  | .Query i => .Query i
  | .QueryPart i j => .QueryPart i j
  | .CheckpointWrite => .CheckpointWrite
  | .Relation => .Relation
  | .Final => .Final

def tx1 (B : Tx1Model.Boundaries) (P : PreparedModel.Boundaries)
    (F : VerifyPrefix.Finish) (D : aspis_core.Digest32 Unit)
    (pub : FirstCaller.Public) (asf8 proof : Slice U8) (k : Usize) (hash : Unit)
    (obs : Option (FirstCaller.Phase → Result Unit)) :
    Result (core.result.Result (alloc.vec.Vec U8) verifier.Error) :=
  Tx1Model.tx1 { B with verify := VerifyPrefix.verify F } P D pub asf8 proof k hash
    (obs.map (fun mark => fun phase => mark (phaseToFirst phase)))

/-- Actual caller acceptance supplies hd, equality of supplied and decoded
public, the helper's serializer success hs, and the matching parsePublic result. -/
theorem first_helper_parsePublic {E : Type} (invalidAccountData : E)
    (B : Tx1Model.Boundaries) (P : PreparedModel.Boundaries)
    (F : VerifyPrefix.Finish) (D : aspis_core.Digest32 Unit)
    (mark : FirstCaller.Phase → Result Unit) (error : verifier.Error → Result E)
    (asf8 proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (h : FirstCaller.first invalidAccountData (tx1 B P F D) mark error asf8 proof k =
      ok (.Ok out)) :
    ∃ s supplied view sem pre initial after challenges bytes wire,
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
        asf8 = ok (.Ok s) ∧
      supplied = PreparationBinding.preparationPublic s ∧
      B.view proof = ok (.Ok view) ∧
      PrefixAdapter.parseAccepted view.semantic = ok (.Ok pre) ∧
      r1_semantic.public_transcript D supplied () pre.c1_root = ok (.Ok initial) ∧
      r1_wire.begin D pre initial = ok (.Ok challenges, after) ∧
      F D supplied pre after challenges
        (some (fun phase => mark (phaseToFirst phase))) = ok (.Ok sem) ∧
      AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (AspisR1TerminalDecoder.PublicBinding.toSerializer s) = ok (.Ok bytes) ∧
      AspisR1.PublicSourceRaw.toWire (AspisR1TerminalDecoder.PublicBinding.projectRaw s) = some wire ∧
      AspisR1.SemanticPublicWire.parsePublic (bytes.val.map AspisR1PublicSerializer.RawBridge431.rawByte) =
        some (AspisR1.SemanticPublicWire.toPublic wire) ∧
      r1_wire.SemanticTranscript.new D () (alloc.vec.Vec.deref bytes) pre.c1_root =
        ok (.Ok initial) := by
  obtain ⟨s, supplied, hd, heq, ht⟩ := FirstCaller.first_success invalidAccountData
    (tx1 B P F D) mark error asf8 proof k out h
  change Tx1Model.tx1 { B with verify := VerifyPrefix.verify F } P D supplied asf8 proof k ()
    (some (fun phase => mark (phaseToFirst phase))) = ok (.Ok out) at ht
  obtain ⟨view, sem, pre, initial, after, challenges, hv, _, hp, hh, hb, hf⟩ :=
    VerifyPrefix.tx1_helper_success B P F D supplied asf8 proof k ()
      (some (fun phase => mark (phaseToFirst phase))) out ht
  have hh' : r1_semantic.public_transcript D (PreparationBinding.preparationPublic s) () pre.c1_root =
      ok (.Ok initial) := heq ▸ hh
  obtain ⟨bytes, wire, hs, hw, hparse, hn⟩ := PreparationBinding.decoder_helper_parsePublic
    D asf8 s () pre.c1_root initial hd hh'
  exact ⟨s, supplied, view, sem, pre, initial, after, challenges, bytes, wire,
    hd, heq, hv, hp, hh, hb, hf, hs, hw, hparse, hn⟩

#print axioms tx1
#print axioms first_helper_parsePublic
end AspisR1PublicPreparation.FirstHelperBinding
