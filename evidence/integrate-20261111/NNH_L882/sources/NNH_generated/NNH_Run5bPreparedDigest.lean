import NNH_Run5bPreparedSlot
import LIBC_PreparedLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bPreparedDigest
open Aeneas Aeneas.Std Result NNH_Run5bCtx
open AspisR1CurrentCaller
/-- Pointwise retained digest association at the corrected runtime environment. -/
theorem digest {W Tx : Type} (c : Ctx W Tx) (parts : Slice (Slice U8)) :
 (InstalledPreparation.retainedDigest
  (AspisS6CurrentFirstInstallation.toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (sdk c)))).digest
  () parts = (LIBC_PreparedLog.digest (envOf c)).digest () parts := rfl
#print axioms digest
end AspisR1.NNH_Run5bPreparedDigest
end
