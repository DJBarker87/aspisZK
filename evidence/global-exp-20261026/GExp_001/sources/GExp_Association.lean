import SdkD_PrepareLower
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_Association
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open SdkD_PrepareLower
variable (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

theorem pure_associated {A : Type} (a : A) : Associated hashv (pure a : Code A) := trivial

theorem lift_associated {A : Type} (r : Result A) :
    Associated hashv (monadLift r : Code A) := by
  cases r <;> trivial

theorem bind_associated {A B : Type} (p : Code A) (k : A → Code B)
    (hp : Associated hashv p) (hk : ∀ a, Associated hashv (k a)) :
    Associated hashv (p >>= k) := by
  induction p with
  | done a => exact hk a
  | step r c ih =>
    cases r with
    | ok a => exact ih a hp
    | fail e => trivial
    | div => trivial
  | digest D h parts c ih => exact ⟨hp.1,fun a => ih a (hp.2 a)⟩

theorem lift_bind_associated {A B : Type} (r : Result A) (k : A → Code B)
    (hk : ∀ a, Associated hashv (k a)) :
    Associated hashv ((monadLift r : Code A) >>= k) :=
  bind_associated hashv _ _ (lift_associated hashv r) hk

theorem digest_associated {H : Type} (D : aspis_core.Digest32 H) (h : H)
    (parts : SdkC_Source.Parts) (law : D.digest h parts = hashv parts) :
    Associated hashv (effects.digest D h parts) := ⟨law,fun _ => trivial⟩

#print axioms pure_associated
#print axioms lift_associated
#print axioms bind_associated
#print axioms lift_bind_associated
#print axioms digest_associated
end AspisR1.GExp_Association
end
