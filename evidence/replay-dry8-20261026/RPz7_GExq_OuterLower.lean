import RPz7_GExq_ChildCode
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

theorem erase_bind_explicit {A B : Type}
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (p : Oracle A) (k : A → Oracle B) :
    CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) ()
      (CheckpointBytes5Effect.bind p k) =
      (CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) () p >>= fun a =>
        CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) () (k a)) := by
  induction p with
  | done a => rfl
  | step r c ih => cases r <;> first | rfl | exact ih _
  | read parts c ih =>
    cases h : hashv parts <;>
      simp only [CheckpointBytes5Effect.bind,CheckpointBytes5Effect.erase,SdkC_Source.dictionary,
        h,bind_tc_ok,bind_tc_fail,bind_tc_div]
    all_goals first | rfl | exact ih _

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
    simp only [lower,erase_bind_explicit,law op good.1,S2W_Trace.erase]
    cases S2W_Trace.invoke sdk op with
    | fail e => rfl
    | div => rfl
    | ok a => exact ih a (good.2 a)

#print axioms erase_bind_explicit
#print axioms erasure
end AspisR1.GExq_OuterLower
end
