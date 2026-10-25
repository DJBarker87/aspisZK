import S2Y_ForestPublic
import S7JoinQueryRows
import CheckpointBytes5Decision
import MultiproofConeFrozen2Stage

/-! Continuation-2 ownership ruling. Each record is a separate child boundary.
Their parameters are the fixed reached child invocation's carriers, not an
arbitrary S2 Inputs record. None has a Required14 field or whole-caller
conclusion. These records are hypotheses, not installed source instances. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_ChildJoins
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- First-entry verifier owns accepted compact-parser provenance. The exact
proof is the argument obtained by accepted owned-call inversion. No universal
ChildInputRetention port on independently chosen caller observations. -/
structure FirstEntryVerifierConeJoin (proof : Slice U8) : Prop where
  parsed : ∃ tr p, OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr = some p

/-- Multiproof child owns its actual physical range calls, including padding.
These are primitive checked-index observations, not the nodeViews conclusion
or an equality of a source batch's output/log with the model batch. The consumer
is MultiproofConeFrozen2Stage.both_batches. -/
structure MultiproofConeJoin (proof0 proof1 : Slice U8)
    (nodes : Nat → Nat → Slice U8) : Prop where
  batch0Ranges : S2Y_OwnedChildren.NodeRanges proof0 nodes 0
  batch1Ranges : S2Y_OwnedChildren.NodeRanges proof1 nodes 1

/-- Compact scan child owns the reached y1 range call. The SAME parsed proof
then derives the scan result by S8JoinFrozenScan.parsed_y1 / y1_scan. -/
structure S8StageConeJoin (proof y1 : Slice U8) : Prop where
  scanArgument : S2Y_OwnedChildren.Y1Range proof y1

/-- S7 owns the primitive accumulator push history. The stage consumer is
S7JoinQueryRows.query_rows_exact; no CallerInvariant is assumed here. -/
structure S7StageConeJoin (old : S8OwnedP6Finish.Weights)
    (state : S7Kani2AccumulatorLoop.BatchedWeights) (sum : S7Kani3CallerTrace.Sum) : Prop where
  pushes : S7Kani3CallerTrace.PushTrace old state sum

/-- Checkpoint child owns its input saved-state provenance, precisely the
existing source-state structure consumed by decision_success_join. This does
not assert saved bytes, persisted account bytes, resume output or a log join. -/
structure CheckpointConeJoin (wp : CheckpointBytes5Writer.Prepared)
    (wa : CheckpointBytes5Writer.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E) : Prop where
  stateProvenance : CheckpointBytes5Join.S1S7S8StateProvenance wp wa pm am

/-- S6's explicitly missing accepted full-forest codec theorem. Neither the
caller publicBytes field nor reconstructed-statement identity is assumed. -/
structure FullForestConeJoin (ops : AdapterRw.Ops) : Prop where
  acceptedRoundtrip : S2Y_ForestPublic.FullForestAcceptedRoundtrip ops

/-- Discharge internal geometry from the separately owned child joins.
No c.nodes/c.y1/Inputs/S2CallerFacts proposition occurs in a hypothesis.
Cross-transaction sameProof is deliberately separate: it is the runtime P2′
consumer's result, not a child source fact. -/
theorem internal_geometry (proof0 proof1 y1 : Slice U8)
    (nodes : Nat → Nat → Slice U8)
    (entry : FirstEntryVerifierConeJoin proof0)
    (multiproof : MultiproofConeJoin proof0 proof1 nodes)
    (scan : S8StageConeJoin proof0 y1)
    (sameProof : bytesOf proof1.val = bytesOf proof0.val) :
    ∃ tr p, OraclePortStoredParserC4.parseReached (bytesOf proof0.val) tr = some p ∧
      (∀ b k, b < 2 → k < 3 → bytesOf (nodes b k).val =
        slice p.wire (OraclePortSelectedDraft.slotStart (3*b+k))
          (32*OraclePortSelectedDraft.capacity (3*b+k))) ∧
      y1 = S8JoinFrozenScan.segment proof0 7031 464 ∧
      S8OwnedP6.check_values_owned y1 = ok (.Ok ()) := by
  obtain ⟨tr,p,parser⟩ := entry.parsed
  have parser1 : OraclePortStoredParserC4.parseReached (bytesOf proof1.val) tr = some p := by
    rw [sameProof]
    exact parser
  have first := S2Y_OwnedChildren.batch_views proof0 nodes 0 tr p parser multiproof.batch0Ranges
  have second := S2Y_OwnedChildren.batch_views proof1 nodes 1 tr p parser1 multiproof.batch1Ranges
  have y := S2Y_ChildGeometry.y1_scan proof0 y1 tr p parser scan.scanArgument.1 scan.scanArgument.2
  refine ⟨tr,p,parser,?_,y.1,y.2⟩
  intro b k hb hk
  have cases : b = 0 ∨ b = 1 := by omega
  rcases cases with h | h
  · subst b; exact first k hk
  · subst b; exact second k hk

#print axioms internal_geometry
end AspisR1.S2W_ChildJoins
end
