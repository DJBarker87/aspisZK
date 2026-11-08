import NNH_HostExec
import NNC_FirstCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_HostFirstWriter
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical NNH_HostCtx NNH_LiteralHost
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

theorem owned (c : Ctx W Tx) (accepted : (S_host L copy std).Accepted1 c (model1 c)) :
 model1 c CPH_Program.verifier c.i.entry.first c.i.data = .ok (.Ok c.world.saved) := by
 exact (PoolT_Write.accepted_verifier_writes_copy (sdk c) (model1 c) (model2 c) (hashv c)
  (NNH_HostCtx.extraction c) copy std NNE_AbortIndicator.allocator c.i.entry CPH_Program.verifier
  c.i.data true true c.world.saved (NNH_HostExec.post c.i c.world.saved) accepted).1

theorem oracle (c : Ctx W Tx) : CheckpointBytes5Inputs.Oracle
 (VTop_Checkpoint.digest (Tx1Q_Install.digest (DrvC_Installation.currentDigest (configuration c)))) () c.sha256 := by
 intro parts digest returned
 change (sdk c).op43 () parts = .ok digest at returned
 rw [(NNH_HostCtx.extraction c).digestSource,S2W_DigestExtraction.digest_eq_hashv] at returned
 exact (DGP_HostDigest.syscall c.sha256).returningValue parts digest returned

theorem writer (c : Ctx W Tx) (accepted : (S_host L copy std).Accepted1 c (model1 c)) :
 ∃ f : S2W_NativeConsolidation.FirstCut,
 NNC_FirstCuts.Facts (sdk c) c.i.entry.first c.world.saved f ∧
 NLP_InputDomain.Root0 c.world.saved.deref f.proof ∧
 NLW_ReaderHeader.decode (bytesOf c.world.saved.val) =
  some (c.sha256 (bytesOf f.proof.val),c.sha256 (bytesOf f.pub.val)) := by
 exact NNC_FirstCuts.writer (configuration c) (model1 c) (model2 c) (hashv c)
  (NNH_HostCtx.extraction c) CPH_Program.verifier c.i.entry.first c.i.data c.world.saved
  c.sha256 (oracle c) (owned L copy std c accepted)
#print axioms owned
#print axioms oracle
#print axioms writer
end AspisR1.NNH_HostFirstWriter
end
