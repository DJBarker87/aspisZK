import NNV_CheckpointEraseCongr
import NNV_CheckpointDigest
import NNV_PreparedStateTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_CurrentCheckpoint
open Aeneas Aeneas.Std Result NNH_Run5bCtx AspisR1CurrentCaller

theorem slot {W Tx : Type} (c : Ctx W Tx) (p : verifier.Prepared) (a : verifier.Accumulator)
 (proof pub : Slice U8) :
 (DrvC_Installation.currentInstalled (configuration c)).op16 (NNV_PreparedAtHost.digest c) p a proof pub () =
 Tx1Q_Install.writer (NNV_PreparedAtHost.digest c) p a proof pub () := rfl

theorem source {W Tx : Type} (c : Ctx W Tx) (a : LIBC_Checkpoint.Args) :
 (DrvC_Installation.currentInstalled (configuration c)).op16 (NNV_PreparedAtHost.digest c)
  (InstalledPreparation.currentPrepared a.1)
  (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc a.2.1))
  (LIBC_Bytes.raw a.2.2.1) (LIBC_Bytes.raw a.2.2.2) () =
 .ok (⟨(LIBC_Checkpoint.output a (envOf c)).val,
  (LIBC_Checkpoint.output a (envOf c)).property⟩ : alloc.vec.Vec U8) := by
 rw [slot]
 unfold Tx1Q_Install.writer
 rw [NNV_PreparedStateTransport.prepared,Tx1Q_Carriers.accumulator_roundtrip]
 unfold Port3_CheckpointInstall.writer
 have same : ∀ parts,
  (VTop_Checkpoint.digest (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c))).digest () parts =
  (LIBC_Checkpoint.digest (envOf c)).digest () parts := fun parts => NNV_CheckpointDigest.source c parts
 rw [NNV_CheckpointEraseCongr.source _ _ () _ same]
 have erased := NNV_CheckpointValue.source a (envOf c)
 exact congrArg (fun out : Result (Slice U8) => do
  let ck ← out
  Result.ok (⟨ck.val,ck.property⟩ : alloc.vec.Vec U8)) erased
#print axioms slot
#print axioms source
end AspisR1.NNV_CurrentCheckpoint
end
