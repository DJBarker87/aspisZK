import NNH_Run5bPreparedModel
import NNH_Run5bPreparedDigest
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PreparedAtHost
open Aeneas Aeneas.Std Result NNH_Run5bCtx AspisR1CurrentCaller
abbrev digest {W Tx : Type} (c : Ctx W Tx) :=
 AspisS6CurrentFirstInstallation.toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (sdk c))
theorem source {W Tx : Type} (c : Ctx W Tx)
 (sem : r1_semantic.Verified Unit) (v : verifier.View)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
 (DrvC_Installation.currentInstalled (configuration c)).op8 (digest c) sem v () g =
 (do let (reply,scratch) ← NGN_Emitted.prepared NHL_PreparedScalars.actual
       (LIBC_PreparedLog.digest (envOf c)) (InstalledPreparation.retainedSem sem)
       (InstalledPreparation.retainedView v) ()
       (AspisR1ClaimPreparedBridge.mapArray InstalledPreparation.retainedE g)
     .ok ((match reply with
       | .Ok p => .Ok (InstalledPreparation.currentPrepared p)
       | .Err e => .Err (InstalledPreparation.currentError e)),
       AspisR1ClaimPreparedBridge.mapArray InstalledPreparation.currentE scratch)) :=
 NNH_Run5bPreparedModel.source c (digest c) sem v g
#print axioms source
end AspisR1.NNV_PreparedAtHost
end
