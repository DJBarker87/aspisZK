import NNH_Run5bCurrentInventory
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bPreparedCore
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller AspisR1PublicPreparation
/-- Erasure of the closed preparation source, retaining exactly its arguments. -/
theorem installed (base : Ops) {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
 (sem : AspisR1CurrentCaller.r1_semantic.Verified H) (v : AspisR1CurrentCaller.verifier.View)
 (hash : H) (g : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
 (BorrowedClaimPrepared.closedInstall base).op8 D sem v hash g =
 BorrowedClaimPrepared.originalNew
  (OriginalSerializerInstallation.withOriginalSerializer BorrowedClaimPrepared.closedSampling)
  AspisS1M31Embedding.Total.embed D sem v hash g :=
 (BorrowedClaimPrepared.closedPreparationCode_installed base D sem v hash g).symm.trans
  (BorrowedClaimPrepared.closedPreparationCode_erasure D sem v hash g)
#print axioms installed
end AspisR1.NNH_Run5bPreparedCore
end
