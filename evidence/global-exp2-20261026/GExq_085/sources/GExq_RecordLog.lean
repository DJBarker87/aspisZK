import GExq_OuterRecord
import SdkC_SourceLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_RecordLog
open Aeneas Aeneas.Std Result GExq_OuterLower

theorem run_bind_explicit {A B : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (p : Oracle A) (k : A → Oracle B) (before : SdkC_Source.Log) :
    SdkC_Source.run hashv (CheckpointBytes5Effect.bind p k) before =
      SdkC_Source.resume hashv (SdkC_Source.run hashv p before) k :=
  SdkC_Source.run_bind hashv p k before

/-- Ghost argument/reply recording preserves the ENTIRE attempted syscall log
on every outcome, including failures and rejected suffix prefixes. -/
theorem log {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (impl : {B : Type} → S2W_Trace.Call B → Oracle B)
    (code : Native A) (events : List GExq_OuterRecord.Event) (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv (GExq_OuterRecord.record impl code events) before).2 =
      (SdkC_Source.run hashv (lower impl code) before).2 := by
  induction code generalizing events before with
  | done a => rfl
  | step r k ih => cases r with
    | fail e => rfl
    | div => rfl
    | ok a => exact ih a events before
  | call op k ih =>
    simp only [GExq_OuterRecord.record,lower,run_bind_explicit]
    generalize actual : SdkC_Source.run hashv (impl op) before = ran
    obtain ⟨result,after⟩ := ran
    cases result with
    | fail e => rfl
    | div => rfl
    | ok a => exact ih a (events ++ GExq_OuterRecord.project op a) after

#print axioms run_bind_explicit
#print axioms log
end AspisR1.GExq_RecordLog
end
