import SAG_DotWeights
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_DotLaw
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators

/-- The actual Stage2 decoder and accumulator weights require no extra
arithmetic law. The remaining frontiers are the concrete slot installation
and interpretation of the 64 source message reads. -/
theorem from_source {W S : Type} (ops : FinishOps S)
    (kernel : AspisR1FinishRelationCurrent.FinishOps W AspisR1FinishDotDecodedProductTrace.PushState)
    (v : verifier.View) (a : verifier.Accumulator) (out : E)
    (f : Fin 64 → AspisWideTower.WideExact)
    (installed : ops.dot = SAG_DotAdapter.sourceDot kernel)
    (length : a.weights.val.length = 64)
    (fields : ∀ (index : Usize) (value : AspisR1FinishDotDecodedProductTrace.FinishE)
      (bound : index.val < 64),
      AspisR1CurrentWide.Proof.finishField v.final_message index = ok value →
      AspisR1CurrentWide.Proof.decodeFinish value = f ⟨index.val,bound⟩)
    (success : ops.dot v.final_message a.weights.deref = ok (.Ok out)) :
    CheckpointBytes5Output.ofE out = ∑ l : Fin 64, f l *
      LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l) := by
  rw [installed] at success
  rw [SAG_DotDecode.e_decode]
  exact SAG_DotAdapter.sourceDot_reader_law kernel v.final_message a.weights.deref out f
    (CheckpointBytes5Output.accumulator a).weights
    (by change a.weights.val.length = 64; exact length)
    fields (SAG_DotWeights.accumulator_read a) success

#print axioms from_source
end AspisR1.SAG_DotLaw
end
