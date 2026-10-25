import GExp_InstalledPrepare
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_LowerLaws
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode

theorem bind_lower {A B : Type} (p : Code A) (k : A → Code B) :
    SdkD_PrepareLower.lower (AspisR1PublicPreparation.PreparedHashCode.bind p k) =
      CheckpointBytes5Effect.bind (SdkD_PrepareLower.lower p) (fun a => SdkD_PrepareLower.lower (k a)) := by
  induction p with
  | done a => rfl
  | step r next ih =>
    simp only [AspisR1PublicPreparation.PreparedHashCode.bind,SdkD_PrepareLower.lower,CheckpointBytes5Effect.bind]
    congr 1
    funext a
    exact ih a
  | digest D hash parts next ih =>
    simp only [AspisR1PublicPreparation.PreparedHashCode.bind,SdkD_PrepareLower.lower,CheckpointBytes5Effect.bind]
    congr 1
    funext a
    exact ih a

theorem lift_lower {A : Type} (r : Result A) :
    SdkD_PrepareLower.lower (monadLift r : Code A) = CheckpointBytes5Effect.liftResult r := rfl

theorem digest_lower {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (hash : H) (parts : SdkC_Source.Parts) :
    SdkD_PrepareLower.lower (effects.digest D hash parts) = CheckpointBytes5Effect.read parts := rfl

#print axioms bind_lower
#print axioms lift_lower
#print axioms digest_lower
end AspisR1.GExp_LowerLaws
end
