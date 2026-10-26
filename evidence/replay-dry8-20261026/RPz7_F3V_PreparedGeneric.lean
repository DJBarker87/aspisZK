import RPz7_F3V_RehashCongr
import RPz7_F3V_TranscriptNew
import RPz7_F3V_Scalar
import RPz7_F3V_Rho
import RPz7_F3V_Queries
import RPz7_S1PreparedCompleteHashErasureV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_PreparedGeneric
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries)
    (claimLaw : ∀ sem y1 inactive powers kappa,
      B.claim D sem y1 inactive powers kappa=
        B.claim (F3U_Rehash.dictionary H D) sem y1 inactive powers kappa)
    (sem : r1_semantic.Verified Hash) (v : verifier.View) (hash : Hash)
    (scratch : Array aspis_core.field.WideExact 29#usize) :
    F3U_Rehash.code H (PreparedSourceEffects.prepare (preparationEffects B Q) D sem v hash scratch)=
      PreparedSourceEffects.prepare (preparationEffects B Q) (F3U_Rehash.dictionary H D) sem v hash scratch := by
  unfold PreparedSourceEffects.prepare preparationEffects
  repeat' first
    | (solve | with_reducible apply F3V_TranscriptNew.same)
    | (solve | with_reducible apply F3V_Scalar.same)
    | (solve | with_reducible apply F3V_Rho.same)
    | (solve | with_reducible apply F3V_Queries.same)
    | (solve |
        change F3U_Rehash.code H (monadLift (B.claim D _ _ _ _ _)) =
          monadLift (B.claim (F3U_Rehash.dictionary H D) _ _ _ _ _)
        rw [F3U_RehashBind.lift,claimLaw])
    | with_reducible apply F3V_RehashCongr.bind
    | intro x
    | (solve | rfl)
    | split

#print axioms same
end AspisR1.F3V_PreparedGeneric
end
