import RowFinish_Control
import Port4D_ReturnedFinish
import RowFinish_Finalization

set_option autoImplicit false
noncomputable section
namespace AspisR1.FinT_Comparisons
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

/-- Reflection needs only the two canonical operands, not a global injectivity law. -/
theorem canonical_eq (x y : E)
    (hx : CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE x) = x)
    (hy : CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE y) = y) :
    x = y ↔ CheckpointBytes5Output.ofE x = CheckpointBytes5Output.ofE y := by
  constructor
  · exact congrArg CheckpointBytes5Output.ofE
  · intro h
    exact hx.symm.trans ((congrArg CheckpointBytes4ReaderFields.sourceE h).trans hy)

#print axioms canonical_eq

/-- Isolate pairing transport from execution normalization. Each premise is
one decoded primitive value or one canonical source comparison. -/
theorem pairing_transport (d : MatchingSupport.Data AspisWideTower.WideExact)
    (decode : E → AspisWideTower.WideExact) (x0 y0 x1 y1 pair value : E)
    (s0 : x0 = y0 ↔ decode x0 = decode y0)
    (s1 : x1 = y1 ↔ decode x1 = decode y1)
    (sp : pair = value ↔ decode pair = decode value)
    (b0 : decode x0 = TwoRoundComparison.boundary d.p0)
    (q0 : decode y0 = RoundPairing.quarter *
      JointFunctionalBinding.claimedValue d.Y d.c0 d.gamma d.kappa)
    (b1 : decode x1 = TwoRoundComparison.boundary d.p1)
    (q1 : decode y1 = RoundPairing.quarter * d.p0.eval d.alpha0)
    (pairing : decode pair = RoundPairing.dot d.f
      (RoundPairing.dualFold (n := 64) d.alpha1
        (RoundPairing.dualFold (n := 256) d.alpha0
          (FunctionalWeights.weights d.F d.F0 d.kappa))))
    (evaluation : decode value = d.p1.eval d.alpha1) :
    (x0 = y0 ∧ x1 = y1 ∧ pair = value) ↔ MatchingSupport.AcceptedPairing d := by
  rw [s0,s1,sp,b0,q0,b1,q1,pairing,evaluation]
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  constructor
  · rintro ⟨h0,h1,hp⟩
    exact ⟨hp.symm,h1,h0⟩
  · rintro ⟨hp,h1,h0⟩
    exact ⟨h0,h1,hp.symm⟩

#print axioms pairing_transport

end AspisR1.FinT_Comparisons
end
