import SdkC_BatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_BatchMapLog
open Aeneas Aeneas.Std Result

theorem log {Err : Type} (f : AspisR1Stage2.verifier.Error → Err)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (body : SdkC_Source.Code (core.result.Result Unit AspisR1Stage2.verifier.Error))
    (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv (SdkC_BatchSource.mapCode f body) before).2=
      (SdkC_Source.run hashv body before).2 := by
  unfold SdkC_BatchSource.mapCode
  rw [SdkC_Source.run_bind]
  cases h : SdkC_Source.run hashv body before with
  | mk result after => cases result <;> simp only [SdkC_Source.resume,SdkC_Source.run] <;> rfl

#print axioms log
end AspisR1.F3N_BatchMapLog
end
