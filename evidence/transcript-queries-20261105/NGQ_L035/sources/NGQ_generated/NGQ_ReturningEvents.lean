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
    Pure.pure,Bind.bind,CheckpointBytes5Effect.instMonadCode,CheckpointBytes5Effect.bind,
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
/-- Pure success, rejection, failure and divergence preserve the already
attempted digest log. There is no successful-decoder premise. -/
theorem pure_suffix_log {A B : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (code : Code A) (finish : A → Result B) (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv (CheckpointBytes5Effect.bind code (fun a => liftResult (finish a))) before).2=
      (SdkC_Source.run hashv code before).2 := by
  induction code generalizing before with
  | done a => cases finish a <;> rfl
  | step r k ih =>
    cases r with
    | ok b => simpa only [CheckpointBytes5Effect.bind,SdkC_Source.run] using ih b before
    | fail error => rfl
    | div => rfl
  | read parts k ih =>
    cases edge : hashv parts with
    | ok reply =>
      simpa only [CheckpointBytes5Effect.bind,SdkC_Source.run,edge] using ih reply (before++[⟨parts,.ok reply⟩])
    | fail error => simp only [CheckpointBytes5Effect.bind,SdkC_Source.run,edge]
    | div => simp only [CheckpointBytes5Effect.bind,SdkC_Source.run,edge]

theorem rejection_keeps16 {A : Type} (digest : SdkC_Source.Parts → SdkC_Source.Digest)
    (state : NGQ_MaterializeChain.Bytes32) (before : SdkC_Source.Log)
    (finish : NGQ_Effects.Blocks × NGQ_Effects.Blocks → Result A) :
    (SdkC_Source.run (fun p => ok (digest p))
      (CheckpointBytes5Effect.bind (NGQ_Effects.materializeCode state) (fun pair => liftResult (finish pair)))
      before).2.length=before.length+16 := by
  rw [pure_suffix_log]
  exact materialize_count digest state before
#print axioms pure_suffix_log
#print axioms rejection_keeps16
end AspisR1.NGQ_ReturningEvents
end
