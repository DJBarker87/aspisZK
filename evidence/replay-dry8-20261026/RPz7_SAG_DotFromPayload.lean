import SAG_DotLaw
import SAG_DotClosed
import RPz7_SAG_EncodedField
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_DotFromPayload
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators

theorem value {W : Type} (ops : FinishOps W) (v : verifier.View)
    (a : verifier.Accumulator) (out : E) (f : Fin 64 → AspisWideTower.WideExact)
    (installed : ops.dot = SAG_DotClosed.source)
    (length : a.weights.val.length = 64)
    (encoded : SelectedFieldSequenceCodec.encodeWide f = MultiproofConeCanonical.bytesOf v.final_message.val)
    (success : ops.dot v.final_message a.weights.deref = ok (.Ok out)) :
    CheckpointBytes5Output.ofE out = ∑ l : Fin 64, f l *
      LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l) :=
  SAG_DotLaw.from_source ops SAG_DotClosed.seed v a out f installed length
    (SAG_EncodedField.value v.final_message f encoded) success

#print axioms value
end AspisR1.SAG_DotFromPayload
end
