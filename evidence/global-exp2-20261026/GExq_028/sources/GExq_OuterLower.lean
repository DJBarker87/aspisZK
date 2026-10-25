import GExq_ChildCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_OuterLower
open Aeneas Aeneas.Std Result
abbrev Native := S2W_Trace.Code
abbrev Oracle := CheckpointBytes5Effect.Code

def Good (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) {A : Type} : Native A → Prop
  | .done _ => True
  | .step r k => match r with
    | .ok a => Good hashv (k a)
    | _ => True
  | .call op k => GExq_ChildCode.Admissible hashv op ∧ ∀ a, Good hashv (k a)

def lower (impl : {A : Type} → S2W_Trace.Call A → Oracle A) {A : Type} : Native A → Oracle A
  | .done a => .done a
  | .step r k => .step r (fun a => lower impl (k a))
  | .call op k => CheckpointBytes5Effect.bind (impl op) (fun a => lower impl (k a))

theorem erasure {A : Type} (sdk : AdapterRw.Ops)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (impl : {B : Type} → S2W_Trace.Call B → Oracle B)
    (law : ∀ {B : Type} (call : S2W_Trace.Call B), GExq_ChildCode.Admissible hashv call →
      CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) () (impl call) = S2W_Trace.invoke sdk call)
    (code : Native A) (good : Good hashv code) :
    CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) () (lower impl code) = S2W_Trace.erase sdk code := by
  induction code with
  | done a => rfl
  | step r k ih =>
    cases r with
    | fail e => rfl
    | div => rfl
    | ok a => exact ih a good
  | call op k ih =>
    simp only [lower,CheckpointBytes5Effect.erase_bind,law op good.1,S2W_Trace.erase]
    cases S2W_Trace.invoke sdk op with
    | fail e => rfl
    | div => rfl
    | ok a => exact ih a (good.2 a)

#print axioms erasure
end AspisR1.GExq_OuterLower
end
