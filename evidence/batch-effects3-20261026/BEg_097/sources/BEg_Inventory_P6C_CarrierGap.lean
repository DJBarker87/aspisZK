import BEg_TailPrefix
import P6C_CarrierGap
/- Focused L166 kernel boundary inventory. No native simulation instance asserted. -/
#check @AspisR1.P6C_CarrierGap.independent
#print axioms AspisR1.P6C_CarrierGap.independent

set_option autoImplicit false
noncomputable section
namespace AspisR1.BEg_RejectedKinds
open Aeneas Aeneas.Std Result AspisR1Stage2 SdkC_Source
open Port3_NativeBatchCalls (Indices Values)

/-- The approved rejection observation applies uniformly to every Rust error
kind at a shared terminal prefix. It does not assert a native prefix join. -/
theorem all_rejected_kinds {S : Type} (call : Parts → S → Result Digest × S)
    (pre : Code (Indices × Values)) (error : verifier.Error) (state : S) (before : Log) :
    let left := BEf_Carrier.run call (pre >>= BEg_TailPrefix.emitted) state before
    let right := BEf_Carrier.run call
      (pre >>= fun pair => CheckpointBytes5Effect.liftResult
        (.ok (.Err error,pair.1,pair.2))) state before
    BEg_Rejected.tailAccepted left.1 = none ∧
      BEg_Rejected.tailAccepted right.1 = none ∧
      left.2 = right.2 ∧ left.2 = (BEf_Carrier.run call pre state before).2 := by
  dsimp only
  rw [BEf_Bind.run,BEf_Bind.run]
  cases h : BEf_Carrier.run call pre state before with
  | mk result effects =>
    cases result with
    | fail e => exact ⟨rfl,rfl,rfl,rfl⟩
    | div => exact ⟨rfl,rfl,rfl,rfl⟩
    | ok pair => exact ⟨rfl,rfl,rfl,rfl⟩

#print axioms all_rejected_kinds
end AspisR1.BEg_RejectedKinds
end
