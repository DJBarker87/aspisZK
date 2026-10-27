import Op4P_Refinement
import Op3I_Install
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Op4P_Install
open AspisR1CurrentCaller

/-- The extracted WHOLE owned scan; only the nominal Parse carrier changes.
The shipped/reference association is the recorded P6 Kani route. -/
def sourceBody (proof : Slice U8) : Result (core.result.Result Unit verifier.Error) := do
  let r ← Op4P_Extract.Op4P_reference.canonical_scan proof
  match r with
  | .Ok () => ok (.Ok ())
  | .Err .Parse => ok (.Err .Parse)

def install (ops : Ops) : Ops := {ops with op4 := sourceBody}

theorem scan_of_success (proof : Slice U8) (length : proof.val.length = 57607)
    (success : sourceBody proof = ok (.Ok ())) :
    OraclePortCompactDraft.scan (MultiproofConeCanonical.bytesOf proof.val) := by
  rw [sourceBody,Op4P_Refinement.reference_total proof length] at success
  split at success
  · assumption
  · simp only [bind_tc_ok] at success
    cases success

theorem other_slots (ops : Ops) : {install ops with op4 := ops.op4} = ops := by
  cases ops
  rfl

theorem installed_scan (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) :
    (RowShape_InstalledSlots.verifierOps (Op3I_Install.install (install ops)) B std).op4 =
      sourceBody := rfl

#print axioms scan_of_success
#print axioms other_slots
#print axioms installed_scan
end AspisR1.Op4P_Install
end
