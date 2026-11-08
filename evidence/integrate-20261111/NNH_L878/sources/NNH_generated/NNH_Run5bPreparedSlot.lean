import NNH_Run5bPreparedCore
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bPreparedSlot
open Aeneas Aeneas.Std Result NNH_Run5bCtx
open AspisR1CurrentCaller

theorem fixed {W Tx H : Type} (c : Ctx W Tx) (D : aspis_core.digest.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
 (DrvC_Installation.currentInstalled (configuration c)).op8 D sem v hash g =
 (BorrowedClaimPrepared.closedInstall (DrvC_Installation.currentInstalled (configuration c))).op8
  D sem v hash g := rfl

theorem source {W Tx H : Type} (c : Ctx W Tx) (D : aspis_core.digest.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
 (DrvC_Installation.currentInstalled (configuration c)).op8 D sem v hash g =
 BorrowedClaimPrepared.originalNew
  (OriginalSerializerInstallation.withOriginalSerializer BorrowedClaimPrepared.closedSampling)
  AspisS1M31Embedding.Total.embed D sem v hash g := by
 rw [fixed c D sem v hash g]
 exact NNH_Run5bPreparedCore.installed _ D sem v hash g
#print axioms fixed
#print axioms source
end AspisR1.NNH_Run5bPreparedSlot
end
