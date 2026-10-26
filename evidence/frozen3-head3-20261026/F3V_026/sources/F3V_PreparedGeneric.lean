import F3V_TranscriptNew
import F3V_Scalar
import F3V_Rho
import F3V_Queries
import S1PreparedCompleteHashErasureV1
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
  simp only [PreparedSourceEffects.prepare,preparationEffects,F3U_RehashBind.bind,F3U_RehashBind.lift]
  repeat' first
    | rfl
    | (fail_if_no_progress simp only [F3U_RehashBind.bind, F3V_TranscriptNew.same, F3V_Scalar.same, F3V_Rho.same, F3V_Queries.same, claimLaw,  PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (fun k => _ >>= k);funext x)
    | (apply congrArg (Code.step _);funext x)
    | split

#print axioms same
end AspisR1.F3V_PreparedGeneric
end
