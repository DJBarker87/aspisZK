import SdkC_Source
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_Offset
open Aeneas Aeneas.Std Result SdkC_Source

/-- The existing history is retained exactly once. Failed final reads appear
in the same suffix regardless of the supplied earlier history. -/
theorem source {A : Type} (hashv : Parts → Result Digest) (code : Code A) (before : Log) :
    SdkC_Source.run hashv code before =
      ((SdkC_Source.run hashv code []).1,before ++ (SdkC_Source.run hashv code []).2) := by
  induction code generalizing before with
  | done a => simp only [SdkC_Source.run,List.append_nil]
  | step r k ih =>
    cases r with
    | ok a => exact ih a before
    | fail e => simp only [SdkC_Source.run,List.append_nil]
    | div => simp only [SdkC_Source.run,List.append_nil]
  | read parts k ih =>
    cases h : hashv parts with
    | fail e => simp only [SdkC_Source.run,h,List.nil_append]
    | div => simp only [SdkC_Source.run,h,List.nil_append]
    | ok digest =>
      simp only [SdkC_Source.run,h,List.nil_append]
      rw [ih digest (before ++ [(⟨parts,.ok digest⟩ : Query)]),
        ih digest [(⟨parts,.ok digest⟩ : Query)]]
      simp only [List.append_assoc]

#print axioms source
end AspisR1.BEf_Offset
end
