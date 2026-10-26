import ARS_QueryTransport
import ARS_WorldCylinder
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_CoverageClass
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Exact classification of the reached-read certificate. This is not a
claim that accidental equality of final values implies this certificate. -/
theorem iff_issued {A : Type} (hashv : Parts → Result Digest)
    (H : Bytes → State) (code : Code A) :
    ARR_OracleCoverage.Covered H hashv code ↔
      ARR_ReturnCoverage.ReturnsOnly (run hashv code []).2 ∧
      ARS_QueryTransport.Agrees H (run hashv code []).2 := by
  constructor
  · intro covered
    have returns := ARR_ReturnCoverage.returns_of_covered H hashv code covered []
      (by intro q member; cases member)
    refine ⟨returns,?_⟩
    intro q member digest returned
    have reads : (flatten q.parts,decodeState digest) ∈ readLog (run hashv code []).2 := by
      apply List.mem_filterMap.mpr
      exact ⟨q,member,by simp only [returned]⟩
    have same := (ARR_OracleCoverage.exact H hashv code covered []).2.1
    simp only [readLog,List.filterMap_nil,List.nil_append] at same
    rw [same] at reads
    exact ARS_WorldCylinder.reads_consistent H (SdkC_Oracle.program code) _ reads
  · rintro ⟨returns,agrees⟩
    exact ARS_QueryTransport.covered hashv H code [] returns agrees

#print axioms iff_issued
end AspisR1.ARS_CoverageClass
end
