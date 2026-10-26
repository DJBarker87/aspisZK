import BEg_Rejected
import BEf_Bind
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEg_TailPrefix
open Aeneas Aeneas.Std Result AspisR1Stage2 SdkC_Source
open Port3_NativeBatchCalls (Indices Values)

def emitted (pair : Indices × Values) :
    Code (core.result.Result Unit verifier.Error × Indices × Values) :=
  CheckpointBytes5Effect.liftResult
    (do let (i,v,p) ← Port4B_Rejection.emittedPadding pair.1 pair.2
        Port4B_Rejection.emittedReturn i v p)

def rust (pair : Indices × Values) :
    Code (core.result.Result Unit verifier.Error × Indices × Values) :=
  CheckpointBytes5Effect.liftResult
    (do let (i,v,p) ← Port4B_Rejection.rustPadding pair.1 pair.2
        Port4B_Rejection.emittedReturn i v p)

/-- Every preceding source pre is kept, not merely a preselected list of
successful queries. A failed pre never reaches either tail. This theorem
is local to the shared-pre/tail shape and assumes no native association. -/
theorem padding {S : Type} (call : Parts → S → Result Digest × S)
    (pre : Code (Indices × Values)) (state : S) (before : Log) :
    let left := BEf_Carrier.run call (pre >>= emitted) state before
    let right := BEf_Carrier.run call (pre >>= rust) state before
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

#print axioms padding
end AspisR1.BEg_TailPrefix
end
