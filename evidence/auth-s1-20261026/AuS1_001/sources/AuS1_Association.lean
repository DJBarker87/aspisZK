import SdkD_PrepareSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Association
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode

/-- Every explicit digest uses the selected partial syscall, on every
continuation. No success, totality, log or authentication law is a field. -/
def Uniform (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) {A : Type} : Code A → Prop
  | .done _ => True
  | .step _ k => ∀ a, Uniform hashv (k a)
  | .digest D hash parts k => D.digest hash parts = hashv parts ∧ ∀ a, Uniform hashv (k a)

theorem pure_uniform (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) {A : Type} (a : A) :
    Uniform hashv (pure a : Code A) := True.intro

theorem lift_uniform (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) {A : Type} (r : Result A) :
    Uniform hashv (monadLift r : Code A) := fun _ => True.intro

theorem digest_uniform (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H) (hash : H) (parts : Slice (Slice U8))
    (law : D.digest hash parts = hashv parts) :
    Uniform hashv (effects.digest D hash parts) := ⟨law,fun _ => True.intro⟩

theorem bind_uniform (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) {A B : Type}
    (p : Code A) (k : A → Code B) (hp : Uniform hashv p) (hk : ∀ a, Uniform hashv (k a)) :
    Uniform hashv (p >>= k) := by
  induction p with
  | done a => exact hk a
  | step r next ih => exact fun a => ih a (hp a)
  | digest D hash parts next ih => exact ⟨hp.1,fun a => ih a (hp.2 a)⟩

theorem associated (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) {A : Type}
    (p : Code A) (hp : Uniform hashv p) : SdkD_PrepareLower.Associated hashv p := by
  induction p with
  | done a => trivial
  | step r next ih => cases r with
    | ok a => exact ih a (hp a)
    | fail e => trivial
    | div => trivial
  | digest D hash parts next ih => exact ⟨hp.1,fun a => ih a (hp.2 a)⟩

#print axioms pure_uniform
#print axioms lift_uniform
#print axioms digest_uniform
#print axioms bind_uniform
#print axioms associated
end AspisR1.AuS1_Association
end
