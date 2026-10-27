import RPz7_SAG_DotFromPayload
import RPz7_SAG_FinalPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_DotFromRead
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun
open scoped BigOperators

theorem value {W : Type} (ops : FinishOps W) (v : verifier.View)
    (a : verifier.Accumulator) (out : E) (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : ErasedPrefix) (d : MatchingSupport.Data AspisWideTower.WideExact)
    (installed : ops.dot = SAG_DotClosed.source)
    (length : a.weights.val.length = 64)
    (aligned : Aligned parsed tr)
    (read : LiteralMatchingData.read (typedRows parsed q tr) = some d)
    (physical : MultiproofConeCanonical.bytesOf v.final_message.val = slice parsed.wire 8007 2048)
    (success : ops.dot v.final_message a.weights.deref = ok (.Ok out)) :
    CheckpointBytes5Output.ofE out = ∑ l : Fin 64, d.f l *
      LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l) := by
  have encoded := SAG_FinalPayload.from_read parsed q tr d aligned read
  exact SAG_DotFromPayload.value ops v a out d.f installed length
    (encoded.trans physical.symm) success

#print axioms value
end AspisR1.SAG_DotFromRead
end
