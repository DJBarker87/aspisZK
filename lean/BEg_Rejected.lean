import BEg_Observation
import BEf_RejectDecoder
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEg_Rejected
open Aeneas Aeneas.Std Result AspisR1Stage2 SdkC_Source
open Port3_NativeBatchCalls (Indices Values)

/-- Scratch is an accepted output only. A rejected tail still retains the
external mutable carrier and log, outside Result. -/
def tailAccepted : Result (core.result.Result Unit verifier.Error × Indices × Values) →
    Option (Indices × Values)
  | .ok (.Ok (),idx,val) => some (idx,val)
  | _ => none

/-- Exact known padding site: equal rejection and ordered effects despite the
unequal error encoding. This is a LOCAL tail law, not full native refinement. -/
theorem padding {S : Type} (call : Parts → S → Result Digest × S)
    (idx : Indices) (val : Values) (state : S) (before : Log) :
    let emitted := BEf_Carrier.run call
      (CheckpointBytes5Effect.liftResult
        (do let (i,v,p) ← Port4B_Rejection.emittedPadding idx val
            Port4B_Rejection.emittedReturn i v p)) state before
    let rust := BEf_Carrier.run call
      (CheckpointBytes5Effect.liftResult
        (do let (i,v,p) ← Port4B_Rejection.rustPadding idx val
            Port4B_Rejection.emittedReturn i v p)) state before
    tailAccepted emitted.1 = none ∧ tailAccepted rust.1 = none ∧
      emitted.2 = rust.2 ∧ emitted.2 = (state,before) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

#print axioms padding
end AspisR1.BEg_Rejected
end
