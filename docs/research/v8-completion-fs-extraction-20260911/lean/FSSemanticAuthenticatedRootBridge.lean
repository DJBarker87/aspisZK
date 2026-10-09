import FSLiveSemanticPrefix
import ExtractionCollectorAuthenticatedReplayable

/-!
# Same-body semantic roots equal authenticated chronological cuts

The semantic prefix and selected Merkle suffix both parse the same submitted
body.  A successful selected suffix additionally compares the two body roots
with the chronological C1/C2 commitment cuts.  This leaf composes those facts;
it does not accept a root-coherence certificate as an input.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.FSSemanticAuthenticatedRootBridge

open FSOracleExecution FSBoundedTranscript
open FSV7PrefixBridge FSV7SelectedBodyScript
open AspisV8Completion.FSLiveSemanticPrefix
open AspisV8Completion.SameBodySemanticWire
open AspisV8Completion.ExtractionCollectorAuthenticatedReplayable
open AspisPool.V7MerkleQueryExtractor

abbrev Bytes := List UInt8
abbrev Position := AspisPool.V7MerkleQueryExtractor.Position

/-- Successful semantic and authentication executions on one body force the
roots consumed by the semantic transcript to be the actual chronological root
cuts.  The executions may begin from different oracle states; this theorem is
the deterministic same-body/root identity, not their chronological splice. -/
theorem successful_runs_bind_semantic_roots
    (positiveTransfer : Bool) (binding : Binding) (body : Bytes)
    (semanticTape merkleTape : FSBoundedTranscript.Tape)
    (semanticOracle merkleOracle : FSBoundedTranscript.Oracle)
    (semantic : FSLiveSemanticPrefix.Success)
    (semanticRun :
      (run semanticTape (semanticScript positiveTransfer binding body)
        semanticOracle).1 = some (.ok semantic))
    (cuts : FSBoundedTranscript.RootCuts) (positions : Fin 22 → Position)
    (trace : AspisPool.V7MerkleQueryGrammar.OrderedRawQueryLog)
    (consistent : FSExposureOrder.LogConsistent merkleOracle)
    (merkleRun :
      (run merkleTape (selected22 cuts positions (encode body)) merkleOracle).1 =
        some trace) :
    ∃ wire, SameBodySemanticWire.parse body = some wire ∧
      wire.roots 0 = (fun byte => cuts.c1 byte) ∧
      wire.roots 1 = (fun byte => cuts.c2 byte) := by
  obtain ⟨semanticWire, semanticParsed, _⟩ :=
    successful_run_has_same_body_wire positiveTransfer binding body semanticTape
      semanticOracle semantic semanticRun
  have selectedRun :
      (run merkleTape (selectedScript cuts positions (encode body)) merkleOracle).1 =
        some trace := by
    simpa only [run_selected22] using merkleRun
  obtain ⟨merkle, _, root0, root1, _⟩ :=
    selected_constructs merkleTape cuts positions (encode body) merkleOracle trace
      consistent selectedRun
  have semanticEq : semanticWire = ofSelected merkle.wire := by
    have selectedParsed :
        AspisV8.SelectedWireBytes.parse (body.map UInt8.toFin) =
          some merkle.wire := by
      simpa only [encode] using merkle.parsed
    unfold SameBodySemanticWire.parse at semanticParsed
    rw [selectedParsed] at semanticParsed
    exact (Option.some.inj semanticParsed).symm
  subst semanticWire
  refine ⟨ofSelected merkle.wire, semanticParsed, ?_, ?_⟩
  · funext byte
    have equal := congrFun root0 byte
    change UInt8.ofFin (merkle.wire.roots 0 byte) = cuts.c1 byte
    rw [equal]
    exact byte_roundtrip _
  · funext byte
    have equal := congrFun root1 byte
    change UInt8.ofFin (merkle.wire.roots 1 byte) = cuts.c2 byte
    rw [equal]
    exact byte_roundtrip _

#print axioms successful_runs_bind_semantic_roots

end AspisV8Completion.FSSemanticAuthenticatedRootBridge
