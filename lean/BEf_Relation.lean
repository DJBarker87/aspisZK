import BEf_Carrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_Relation
open Aeneas Aeneas.Std Result SdkC_Source

/-- Forward simulation for arbitrary mutable carriers, including failed reads.
This is a proof rule; a native carrier instance must supply its local law. -/
theorem simulate {S T A : Type}
    (left : Parts → S → Result Digest × S)
    (right : Parts → T → Result Digest × T)
    (R : S → T → Prop)
    (step : ∀ parts s t, R s t →
      (left parts s).1 = (right parts t).1 ∧ R (left parts s).2 (right parts t).2)
    (code : Code A) (s : S) (t : T) (related : R s t) (before : Log) :
    (BEf_Carrier.run left code s before).1 = (BEf_Carrier.run right code t before).1 ∧
    (BEf_Carrier.run left code s before).2.2 = (BEf_Carrier.run right code t before).2.2 ∧
    R (BEf_Carrier.run left code s before).2.1 (BEf_Carrier.run right code t before).2.1 := by
  induction code generalizing s t before with
  | done a => exact ⟨rfl,rfl,related⟩
  | step r k ih =>
    cases r with
    | ok a => exact ih a s t related before
    | fail e => exact ⟨rfl,rfl,related⟩
    | div => exact ⟨rfl,rfl,related⟩
  | read parts k ih =>
    obtain ⟨same,next⟩ := step parts s t related
    cases hl : left parts s with
    | mk a s' =>
      cases hr : right parts t with
      | mk b t' =>
        simp only [hl,hr] at same next
        subst b
        simp only [BEf_Carrier.run,hl,hr]
        cases a with
        | ok digest => exact ih digest s' t' next (before ++ [⟨parts,.ok digest⟩])
        | fail e => exact ⟨rfl,rfl,next⟩
        | div => exact ⟨rfl,rfl,next⟩

#print axioms simulate
end AspisR1.BEf_Relation
end
