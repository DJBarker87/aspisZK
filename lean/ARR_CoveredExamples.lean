import ARR_ReturnCoverage
import F3U_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARR_CoveredExamples
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

/-- Model-only non-vacuity of the reached-read certificate. The dictionary
varies WITH H; this theorem does not instantiate fixed native extraction. -/
theorem ideal_dictionary {A : Type} (H : Bytes → State) (code : Code A) :
    ARR_OracleCoverage.Covered H (F3U_Oracle.hashv H) code := by
  induction code with
  | done x => trivial
  | step r k ih =>
    cases r with
    | ok x => exact ih x
    | fail e => trivial
    | div => trivial
  | read parts k ih => exact ⟨rfl,ih _⟩

/-- Coverage includes source rejection. It does not filter to accepted runs. -/
theorem rejected {A : Type} (H : Bytes → State)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (error : Error) (k : Unit → Code A) :
    ARR_OracleCoverage.Covered H hashv (.step (.fail error : Result Unit) k) := by
  trivial

/-- Its real attempted log is empty, so returning-only is inhabited even when
source acceptance is impossible. This is NOT headline fixture non-vacuity. -/
theorem rejected_returns {A : Type}
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (error : Error) (k : Unit → Code A) :
    ARR_ReturnCoverage.ReturnsOnly
      (SdkC_Source.run hashv (.step (.fail error : Result Unit) k) []).2 := by
  intro q member
  cases member

#print axioms ideal_dictionary
#print axioms rejected
#print axioms rejected_returns
end AspisR1.ARR_CoveredExamples
end
