import NGQ_MaterializeChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGQ_ReturningEvents
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

/-- Returning oracle only: this is not an assumption of runtime totality. -/
theorem chain_count (digest : SdkC_Source.Parts → SdkC_Source.Digest)
    (state : NGQ_MaterializeChain.Bytes32) (before : SdkC_Source.Log) :
    (SdkC_Source.run (fun p => ok (digest p))
      (NGQ_MaterializeChain.chain state) before).2.length=before.length+16 := by
  simp only [NGQ_MaterializeChain.chain,NGQ_MaterializeChain.pair,
    Bind.bind,CheckpointBytes5Effect.instMonadCode,CheckpointBytes5Effect.bind,
    CheckpointBytes5Effect.read,SdkC_Source.run,List.length_append,List.length_cons,List.length_nil]
  omega

/-- Full emitted materialization has all sixteen chronological attempts when
its calls return. Decoder rejection occurs later and cannot erase this log. -/
theorem materialize_count (digest : SdkC_Source.Parts → SdkC_Source.Digest)
    (state : NGQ_MaterializeChain.Bytes32) (before : SdkC_Source.Log) :
    (SdkC_Source.run (fun p => ok (digest p))
      (NGQ_Effects.materializeCode state) before).2.length=before.length+16 := by
  rw [← NGQ_MaterializeChain.run]
  exact chain_count digest state before
#print axioms chain_count
#print axioms materialize_count
end AspisR1.NGQ_ReturningEvents
end
