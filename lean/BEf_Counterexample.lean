import BEf_RejectDecoder
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_Counterexample
open Aeneas Aeneas.Std Result AspisR1Stage2 SdkC_Source
open Port3_NativeBatchCalls (Indices Values)

/-- An all-Result equality for these two source-local rejected-tail encodings
is false, even when carrier and prior history agree exactly. Native reached
fixtures and the source-slice checks are separate evidence, not hypotheses
silently asserted by this theorem. -/
theorem rejected_batch_tail {S : Type} (call : Parts → S → Result Digest × S)
    (idx : Indices) (val : Values) (state : S) (before : Log) :
    BEf_Carrier.run call
      (CheckpointBytes5Effect.liftResult
        (do let (i,v,p) ← Port4B_Rejection.emittedPadding idx val
            Port4B_Rejection.emittedReturn i v p)) state before ≠
    BEf_Carrier.run call
      (CheckpointBytes5Effect.liftResult
        (do let (i,v,p) ← Port4B_Rejection.rustPadding idx val
            Port4B_Rejection.emittedReturn i v p)) state before := by
  obtain ⟨emitted,native⟩ := BEf_RejectDecoder.padding call idx val state before
  rw [emitted,native]
  intro same
  have impossible := congrArg Prod.fst same
  cases impossible

theorem inhabited :
    ∃ (idx : Indices) (val : Values),
      Port4B_Rejection.emittedPadding idx val ≠ Port4B_Rejection.rustPadding idx val :=
  ⟨Array.repeat 16#usize 0#u32,Array.repeat 16#usize (Array.repeat 32#usize 0#u8),
    Port4B_Rejection.padding_branch_differs _ _⟩

#print axioms rejected_batch_tail
#print axioms inhabited
end AspisR1.BEf_Counterexample
end
