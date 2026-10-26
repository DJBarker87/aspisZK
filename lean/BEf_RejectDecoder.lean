import Port4B_Rejection
import BEf_Carrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_RejectDecoder
open Aeneas Aeneas.Std Result AspisR1Stage2 SdkC_Source
open Port3_NativeBatchCalls (Indices Values)

/-- The two literal pending-return encodings retain the same earlier history
and carrier, while disagreeing on full Result. This is the known emitted-tail
mismatch, not a proof of complete native batch reachability. -/
theorem padding {S : Type} (call : Parts → S → Result Digest × S)
    (idx : Indices) (val : Values) (state : S) (before : Log) :
    BEf_Carrier.run call
      (CheckpointBytes5Effect.liftResult
        (do let (i,v,p) ← Port4B_Rejection.emittedPadding idx val
            Port4B_Rejection.emittedReturn i v p)) state before =
      (.fail .panic,state,before) ∧
    BEf_Carrier.run call
      (CheckpointBytes5Effect.liftResult
        (do let (i,v,p) ← Port4B_Rejection.rustPadding idx val
            Port4B_Rejection.emittedReturn i v p)) state before =
      (.ok (.Err verifier.Error.Parse,idx,val),state,before) := by
  constructor <;> rfl

#print axioms padding
end AspisR1.BEf_RejectDecoder
end
