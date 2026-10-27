import JGx_Natives
import JGx_CallerSeed
import JGx_ProofAccount
import JFv_RuntimeWitness
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Runtime
open Aeneas Aeneas.Std Result DrvC_Installation

/-- Actual extracted native tuple with inherited runtime model. This asserts
no wrapper acceptance, raw game/source join, or 100-bit security result. -/
theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (headerBytes : Array U8 688#usize) :
    S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err))
      (JGx_Natives.first (JGx_CallerSeed.value c) err) (JGx_Natives.second (JGx_CallerSeed.value c) err)
      (F3U_Oracle.hashv JFp_SHADigest.digest) ∧
    CPH_Game.DeployedPairExecution (JFv_World.observations (JGx_ProofAccount.value headerBytes)) false true
      (JFv_World.e1 (JGx_ProofAccount.value headerBytes)) (JFv_World.e2 (JGx_ProofAccount.value headerBytes))
      JFv_World.saved [] (JGx_Natives.first (JGx_CallerSeed.value c) err)
      (JGx_Natives.second (JGx_CallerSeed.value c) err) CPH_FixtureData.copy CPH_FixtureData.allocator CPH_Program.verifier :=
  ⟨JGx_Natives.extraction _ err,JFv_World.game _ _ _⟩
#print axioms source
end AspisR1.JGx_Runtime
end
