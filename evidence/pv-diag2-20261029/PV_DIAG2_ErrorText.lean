import PV_DIAG2_Exit
set_option autoImplicit false
namespace PV_DIAG2
open Aeneas Aeneas.Std Result
open R1Z ProverCommitRetry34

/-- All eleven native verifier Error variants are field-free. This is the
owned model of their complete deployed derived Debug literal selection. -/
def nativeUnitDebug : ProverRwFull.verifier.Error → String
 | .Parse => "Parse"
 | .Semantic => "Semantic"
 | .Transcript => "Transcript"
 | .Relation => "Relation"
 | .Merkle => "Merkle"
 | .Query => "Query"
 | .Checkpoint => "Checkpoint"
 | .Allocation => "Allocation"
 | .Rejected => "Rejected"
 | .AttemptsExhausted => "AttemptsExhausted"
 | .Entropy => "Entropy"

theorem native_debug_join (e : ProverRwFull.verifier.Error) :
 nativeUnitDebug e = spelling (exportError (ProverRwRetryModel.error e)) := by cases e <;> rfl

/-- A single native variant determines its entire Debug operand. Nothing in
this theorem asserts that the choice of variant or its occurrence is public. -/
theorem variant_debug_public (left right : ProverRwFull.verifier.Error)
    (samePublicVariant : left = right) : nativeUnitDebug left = nativeUnitDebug right :=
 congrArg nativeUnitDebug samePublicVariant

/-- The Error spelling installed in the instrumented reporting path is
exactly the native unit-enum Debug string, conditional on that returned code. -/
theorem native_report_disabled (e : ProverRwFull.verifier.Error) (pcs : List Nat) :
 reportError (exportError (ProverRwRetryModel.error e)) pcs "" false =
 ⟨[.returned (exportError (ProverRwRetryModel.error e)),
  .stderr ("Error: " ++ nativeUnitDebug e ++ "\n")],.value 1⟩ := by
 rw [report_disabled,native_debug_join]

/-- No ActivePole payload reaches the unit Error Debug interface. The
native source maps that branch to Rejected before retry classification. -/
theorem rejected_debug_literal : nativeUnitDebug .Rejected = "Rejected" := rfl

theorem exhaustion_debug_literal : nativeUnitDebug .AttemptsExhausted = "AttemptsExhausted" := rfl

theorem entropy_debug_literal : nativeUnitDebug .Entropy = "Entropy" := rfl

#print axioms native_debug_join
#print axioms variant_debug_public
#print axioms native_report_disabled
#print axioms rejected_debug_literal
#print axioms exhaustion_debug_literal
#print axioms entropy_debug_literal
end PV_DIAG2
