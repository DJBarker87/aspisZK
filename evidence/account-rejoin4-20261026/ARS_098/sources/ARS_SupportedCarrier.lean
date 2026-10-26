import ARS_Carrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_SupportedCarrier
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_D189Consolidation

/-- All three original byte carriers, derived on the supported entry.
Checkpoint bytes are the actual TX2 entry buffer, not an invented RunView field. -/
theorem deployed {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (n : ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
    (std : S2W_TrustedStd.TrustedStd copy)
    (run : F3T_Experiment.RunView)
    (observed : (eval H (runtime (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2 = some run) :
    run.2.1.stored = (eval H (submission a)).2.stored ∧
    run.2.1.physical.bytes = (eval H (submission a)).2.publicBytes ∧
    MultiproofConeCanonical.bytesOf
      ((eval H (a.second (eval H a.first).2 n.saved n.post1 n.final1)).2.entry.buffers
        ((eval H (a.second (eval H a.first).2 n.saved n.post1 n.final1)).2.entry.handles 6).1).val =
        MultiproofConeCanonical.bytesOf n.saved.val := by
  have bytes := ARS_Carrier.projection (FIp_Install.configuration err c r) hashv copy allocator
    CPH_Program.verifier a H run observed
  exact ⟨bytes.1,bytes.2,ARS_Carrier.checkpoint c err r hashv copy std allocator native1 native2 extraction
    a H n.saved n.post1 n.post2 n.final1 n.final2 n.accepted1 n.accepted2 n.p n.t n.u n.actions n.game n.RuntimePersistence⟩

#print axioms deployed
end AspisR1.ARS_SupportedCarrier
end
