import RPz8_GExp_LowerLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_RunPrefix
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

theorem run_append {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (code : Code A) (left right : SdkC_Source.Log) :
    SdkC_Source.run hashv code (left ++ right) =
      ((SdkC_Source.run hashv code right).1,left ++ (SdkC_Source.run hashv code right).2) := by
  induction code generalizing right with
  | done a => rfl
  | step r k ih => cases r with
    | ok a => exact ih a right
    | fail e => rfl
    | div => rfl
  | read parts k ih =>
    cases actual : hashv parts with
    | ok digest =>
      simp only [SdkC_Source.run,actual,List.append_assoc]
      exact ih digest (right ++ [⟨parts,.ok digest⟩])
    | fail e => simp only [SdkC_Source.run,actual,List.append_assoc]
    | div => simp only [SdkC_Source.run,actual,List.append_assoc]

#print axioms run_append
end AspisR1.GExp_RunPrefix
end
