import ARS_QueryTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_QueryCost
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Equality counts attempts, with repeats, rather than distinct addresses. -/
theorem count {A : Type} (hashv : Parts → Result Digest)
    (H : Bytes → State) (code : Code A)
    (returns : ARR_ReturnCoverage.ReturnsOnly (run hashv code []).2)
    (agrees : ARS_QueryTransport.Agrees H (run hashv code []).2) :
    (eval H (SdkC_Oracle.program code)).1.length = (run hashv code []).2.length := by
  have addresses := (ARS_QueryTransport.exact hashv H code returns agrees).2.2
  have lengths := congrArg List.length addresses
  simpa only [RPx_AttemptPrefix.addresses,List.length_map] using lengths.symm

/-- Any functional of the full original result, ordered read log, and query
count is preserved. This does not rename a longer ideal suffix as native work. -/
theorem law {A V : Type} (hashv : Parts → Result Digest)
    (H : Bytes → State) (code : Code A)
    (returns : ARR_ReturnCoverage.ReturnsOnly (run hashv code []).2)
    (agrees : ARS_QueryTransport.Agrees H (run hashv code []).2)
    (observe : Result A → List (Bytes × State) → Nat → V) :
    observe (eval H (SdkC_Oracle.program code)).2
      (eval H (SdkC_Oracle.program code)).1 (eval H (SdkC_Oracle.program code)).1.length =
    observe (run hashv code []).1 (readLog (run hashv code []).2) (run hashv code []).2.length := by
  obtain ⟨result,reads,_⟩ := ARS_QueryTransport.exact hashv H code returns agrees
  rw [← result,← reads,count hashv H code returns agrees]

#print axioms count
#print axioms law
end AspisR1.ARS_QueryCost
end
