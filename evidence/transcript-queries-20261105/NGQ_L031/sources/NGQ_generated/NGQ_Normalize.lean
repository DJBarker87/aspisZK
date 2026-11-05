import NGQ_Effects
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGQ_Normalize
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

/-- Remove only successful pure steps. Read occurrences, including unsuccessful
calls, remain in exactly their original order. -/
def normalize {A : Type} : Code A → Code A
 | .done a => .done a
 | .step r k => match r with
   | .ok b => normalize (k b)
   | .fail e => .step (.fail e) (fun b => normalize (k b))
   | .div => .step .div (fun b => normalize (k b))
 | .read parts k => .read parts (fun d => normalize (k d))

theorem run {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (code : Code A) (before : SdkC_Source.Log) :
    SdkC_Source.run hashv (normalize code) before=SdkC_Source.run hashv code before := by
  induction code generalizing before with
  | done a => rfl
  | step r k ih =>
    cases r with
    | ok b => simpa only [normalize,SdkC_Source.run] using ih b before
    | fail e => rfl
    | div => rfl
  | read parts k ih =>
    cases edge : hashv parts with
    | ok d => simpa only [normalize,SdkC_Source.run,edge] using ih d (before++[⟨parts,.ok d⟩])
    | fail e => simp only [normalize,SdkC_Source.run,edge]
    | div => simp only [normalize,SdkC_Source.run,edge]

#print axioms run
end AspisR1.NGQ_Normalize
end
