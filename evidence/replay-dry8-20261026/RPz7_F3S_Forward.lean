import RPz7_F3R_SdkPure
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_Forward
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
 theorem bind_log {A B : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (p : Code A) (k : A → Code B) (a : A)
    (success : erase (SdkC_Source.dictionary hashv) () p=ok a) :
    SdkC_Source.readLog (SdkC_Source.run hashv (CheckpointBytes5Effect.bind p k) []).2=
      SdkC_Source.readLog (SdkC_Source.run hashv p []).2 ++
      SdkC_Source.readLog (SdkC_Source.run hashv (k a) []).2 := by
  have runLaw := SdkC_Source.run_bind hashv p k []
  have native : (SdkC_Source.run hashv p []).1=ok a := (SdkC_Source.erasure hashv p []).trans success
  change SdkC_Source.run hashv (CheckpointBytes5Effect.bind p k) [] = _ at runLaw
  rw [runLaw]
  simp only [SdkC_Source.resume,native]
  have shifted := GExp_RunPrefix.run_append hashv (k a) (SdkC_Source.run hashv p []).2 []
  simp only [List.append_nil] at shifted
  rw [shifted,SdkC_Oracle.readLog_append]
 theorem lift_ok {A B : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (a : A) (k : A → Code B) (before : SdkC_Source.Log) :
    SdkC_Source.run hashv (CheckpointBytes5Effect.bind (liftResult (ok a)) k) before=
      SdkC_Source.run hashv (k a) before := rfl
#print axioms lift_ok
#print axioms bind_log
end AspisR1.F3S_Forward
end
