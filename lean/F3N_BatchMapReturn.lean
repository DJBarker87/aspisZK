import F3N_BatchMapLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_BatchMapReturn
open Aeneas Aeneas.Std Result

theorem accepted {Err : Type} (f : AspisR1Stage2.verifier.Error → Err)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (body : SdkC_Source.Code (core.result.Result Unit AspisR1Stage2.verifier.Error))
    (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv (SdkC_BatchSource.mapCode f body) before).1=ok (.Ok ()) ↔
      (SdkC_Source.run hashv body before).1=ok (.Ok ()) := by
  unfold SdkC_BatchSource.mapCode
  rw [SdkC_Source.run_bind]
  cases h : SdkC_Source.run hashv body before with
  | mk result after =>
    cases result with
    | fail e => simp only [SdkC_Source.resume,Result.fail.injEq,reduceCtorEq]
    | div => simp only [SdkC_Source.resume,reduceCtorEq]
    | ok value =>
      cases value with
      | Ok u => cases u;constructor <;> intro _ <;> rfl
      | Err e => constructor <;> intro impossible <;> cases impossible

#print axioms accepted
end AspisR1.F3N_BatchMapReturn
end
