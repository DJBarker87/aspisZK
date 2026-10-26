import ARU_Returning
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEk_Returning
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

/-- Existing SdkC/ARU computed Returning packets supply exactly the queried
agreement needed by the new local export. No second log is selected. -/
theorem agrees {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (value : A) (returning : SdkC_BatchPair.Returning hashv H code value) :
    ARS_QueryTransport.Agrees H (run hashv code []).2 := by
  intro q member digest returned
  by_contra bad
  apply returning.2.2 (flatten q.parts) (decodeState digest) bad
  apply List.mem_filterMap.mpr
  exact ⟨q,member,by simp only [returned]⟩

#print axioms agrees
end AspisR1.BEk_Returning
end
