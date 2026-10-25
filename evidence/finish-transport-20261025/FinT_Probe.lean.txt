import FinT_Comparisons
import FinT_Returned
import Port4D_ReturnedFinish
import RowFinish_Finalization

set_option autoImplicit false
noncomputable section
namespace AspisR1.FinT_Probe
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
open RowFinish_Control
attribute [local instance] Classical.propDecidable
attribute [local irreducible] QueryAccumulator.run QueryAccumulator.run22
  QueryResidualBridge.values QueryResidualBridge.basis
  OraclePortCheckpointStateC3.write OraclePortCheckpointStateC3.advance
variable {W : Type}

attribute [local irreducible] CheckpointBytes5Output.ofE CheckpointBytes4ReaderFields.sourceE

theorem gates (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (alpha0 alpha1 : E)
    (r0 : RoundValues ops v.round0 alpha0 p.claim)
    (r1 : RoundValues ops v.round1 alpha1 r0.value)
    (weights : W) (alphas : Slice E) (pair : E)
    (s2 : p.variant = .S2)
    (ha0 : Array.index_usize p.alpha 0#usize = ok alpha0)
    (ha1 : Array.index_usize p.alpha 1#usize = ok alpha1)
    (hw : ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights))
    (has : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas)
    (hp : ops.pair weights alphas v.final_message p.kappa = ok (.Ok pair))
    (d : MatchingSupport.Data AspisWideTower.WideExact)
    (laws : Port4D_Pairing.PairingLaws (Port3_FinishStage.release ops)
      CheckpointBytes5Output.ofE v p d)
    (c0 : CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE r0.lhs) = r0.lhs)
    (c1 : CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE r0.rhs) = r0.rhs)
    (c2 : CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE r1.lhs) = r1.lhs)
    (c3 : CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE r1.rhs) = r1.rhs)
    (c4 : CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE pair) = pair)
    (c5 : CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE r1.value) = r1.value) :
    True := by
  have b0 : CheckpointBytes5Output.ofE r0.lhs = TwoRoundComparison.boundary d.p0 := laws.round0.boundary r0.c0 r0.c4 r0.lhs r0.field0 r0.field4 r0.add
  have b1 : CheckpointBytes5Output.ofE r1.lhs = TwoRoundComparison.boundary d.p1 := laws.round1.boundary r1.c0 r1.c4 r1.lhs r1.field0 r1.field4 r1.add
  have quarter0 : CheckpointBytes5Output.ofE r0.rhs = RoundPairing.quarter * CheckpointBytes5Output.ofE p.claim := laws.round0.quarter r0.quarter p.claim r0.rhs r0.quarter_run r0.multiply
  have quarter1 : CheckpointBytes5Output.ofE r1.rhs = RoundPairing.quarter * CheckpointBytes5Output.ofE r0.value := laws.round1.quarter r1.quarter r0.value r1.rhs r1.quarter_run r1.multiply
  have ev0 : CheckpointBytes5Output.ofE r0.value = d.p0.eval (CheckpointBytes5Output.ofE alpha0) := laws.round0.eval alpha0 r0.value r0.evaluate
  have ev1 : CheckpointBytes5Output.ofE r1.value = d.p1.eval (CheckpointBytes5Output.ofE alpha1) := laws.round1.eval alpha1 r1.value r1.evaluate
  set_option pp.explicit true in
    trace_state
  trivial

#print axioms gates
end AspisR1.FinT_Probe
end
