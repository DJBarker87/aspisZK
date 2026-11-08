import NNV_PreparedAtHost
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_CurrentBatchSource
open Aeneas Aeneas.Std Result NNH_Run5bCtx AspisR1CurrentCaller

theorem slot {W Tx : Type} (c : Ctx W Tx) {H : Type}
 (D : aspis_core.digest.Digest32 H) (proof : Slice U8) (p : verifier.Prepared)
 (folded : Array U8 32#usize) (batch : Usize) (hash : H) :
 (DrvC_Installation.currentInstalled (configuration c)).op6 D proof p folded batch hash =
 Op5T_Install.currentBatch Port4B_Install.leaves D proof p folded batch hash := rfl

theorem source {W Tx : Type} (c : Ctx W Tx) (proof : Slice U8) (p : LIB_VCarriers.Prepared)
 (folded : Array U8 32#usize) (batch : Usize) :
 (DrvC_Installation.currentInstalled (configuration c)).op6 (NNV_PreparedAtHost.digest c)
  proof (InstalledPreparation.currentPrepared p) folded batch () =
 Op5T_Install.mapResult Op5T_Install.currentError
  (Op5T_Install.body Port4B_Install.leaves
   (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)) proof p.queries p.roots folded batch ()) := by
 rw [slot,Op5T_Concrete.current_source]
 rfl
#print axioms slot
#print axioms source
end AspisR1.NNV_CurrentBatchSource
end
