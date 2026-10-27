import RPt_BEi_Execution
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEi_ExecutionComplete
open Aeneas Aeneas.Std Result SdkC_Source BEi_Execution

/-- No total-syscall premise: failure and divergence are terminal cuts. -/
theorem complete {S A : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (state : S) (before : Log) :
    Executes call code state before
      (BEf_Carrier.run call code state before).1
      (BEf_Carrier.run call code state before).2.1
      (BEf_Carrier.run call code state before).2.2 := by
  induction code generalizing state before with
  | done a => exact .done a state before
  | step r k ih =>
    cases r with
    | ok a => exact .stepOk a k _ _ _ _ _ (ih a state before)
    | fail e => exact .stepFail e k state before
    | div => exact .stepDiv k state before
  | read parts k ih =>
    cases called : call parts state with
    | mk answer after =>
      cases answer with
      | ok digest =>
        simpa only [BEf_Carrier.run,called] using
          (Executes.readOk parts k state after _ before _ digest _ called
            (ih digest after (before ++ [⟨parts,.ok digest⟩])))
      | fail error =>
        simpa only [BEf_Carrier.run,called] using
          (Executes.readFail parts k state after before error called)
      | div =>
        simpa only [BEf_Carrier.run,called] using
          (Executes.readDiv parts k state after before called)

#print axioms complete
end AspisR1.BEi_ExecutionComplete
end
