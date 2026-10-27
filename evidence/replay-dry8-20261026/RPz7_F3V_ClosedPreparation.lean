import RPz7_F3V_PreparedGeneric
import RPz7_F3V_OracleDictionary
import RPz7_S1ClosedPreparationHashCodeV1
import RPz7_F3V_ClaimPublic
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_ClosedPreparation
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (sem : AspisR1CurrentCaller.r1_semantic.Verified Hash)
    (v : AspisR1CurrentCaller.verifier.View) (hash : Hash)
    (scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
    F3U_Rehash.code H (AspisR1CurrentCaller.BorrowedClaimPrepared.closedPreparationCode D sem v hash scratch)=
      AspisR1CurrentCaller.BorrowedClaimPrepared.closedPreparationCode
        (F3V_OracleDictionary.current H D) sem v hash scratch := by
  simp only [AspisR1CurrentCaller.BorrowedClaimPrepared.closedPreparationCode,
    F3U_RehashBind.bind,F3V_OracleDictionary.retained]
  rw [F3V_PreparedGeneric.same H _ _ _ (fun _ _ _ _ _ =>
    F3V_ClaimPublic.same _ _ _ _ _ _ _)]
  apply congrArg (fun k => _ >>= k)
  funext x
  rfl

#print axioms same
end AspisR1.F3V_ClosedPreparation
end
