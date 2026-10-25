import GExp_RunPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_LowerTrace
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem log {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (code : PreparedHashCode.Code A) (association : SdkD_PrepareLower.Associated hashv code) :
    SdkC_Source.readLog (SdkC_Source.run hashv (SdkD_PrepareLower.lower code) []).2 =
      PreparedHashCode.observe (PreparedHashCode.run code).1 := by
  induction code with
  | done a => rfl
  | step r k ih => cases r with
    | ok a => exact ih a association
    | fail e => rfl
    | div => rfl
  | digest D hash parts k ih =>
    cases actual : hashv parts with
    | ok digest =>
      have source : D.digest hash parts = ok digest := association.1.trans actual
      simp only [SdkD_PrepareLower.lower,SdkC_Source.run,actual,
        PreparedHashCode.run,source]
      have frame := GExp_RunPrefix.run_append hashv (SdkD_PrepareLower.lower (k digest))
        [⟨parts,.ok digest⟩] []
      simp only [List.append_nil] at frame
      simp only [List.nil_append]
      rw [frame,SdkC_Oracle.readLog_append,ih digest (association.2 digest)]
      rfl
    | fail e =>
      have source : D.digest hash parts = .fail e := association.1.trans actual
      simp only [SdkD_PrepareLower.lower,SdkC_Source.run,actual,
        PreparedHashCode.run,source]
      rfl
    | div =>
      have source : D.digest hash parts = .div := association.1.trans actual
      simp only [SdkD_PrepareLower.lower,SdkC_Source.run,actual,
        PreparedHashCode.run,source]
      rfl

#print axioms log
end AspisR1.GExp_LowerTrace
end
