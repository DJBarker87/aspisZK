import RPt_BEf_Carrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_Bind
open Aeneas Aeneas.Std Result SdkC_Source

def continueRun {S A B : Type} (call : Parts → S → Result Digest × S)
    (k : A → Code B) (out : Result A × S × Log) : Result B × S × Log :=
  match out.1 with
  | .ok a => BEf_Carrier.run call (k a) out.2.1 out.2.2
  | .fail e => (.fail e,out.2.1,out.2.2)
  | .div => (.div,out.2.1,out.2.2)

/-- Sequential composition preserves the carrier and complete rejected prefix. -/
theorem run {S A B : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (k : A → Code B) (state : S) (before : Log) :
    BEf_Carrier.run call (code >>= k) state before =
      continueRun call k (BEf_Carrier.run call code state before) := by
  induction code generalizing state before with
  | done a => rfl
  | step r next ih =>
    cases r with
    | ok a => exact ih a state before
    | fail e => rfl
    | div => rfl
  | read parts next ih =>
    change BEf_Carrier.run call (.read parts (fun d => next d >>= k)) state before = _
    simp only [BEf_Carrier.run]
    cases h : call parts state with
    | mk answer after =>
      simp only []
      cases answer with
      | ok digest => exact ih digest after (before ++ [⟨parts,.ok digest⟩])
      | fail e => rfl
      | div => rfl

#print axioms run
end AspisR1.BEf_Bind
end
