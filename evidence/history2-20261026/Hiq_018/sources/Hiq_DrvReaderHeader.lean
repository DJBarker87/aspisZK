import DrvC_Installation
import CPhy_Header
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_DrvReaderHeader
open Aeneas Aeneas.Std Result S2W_NativeConsolidation DrvC_Installation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep MultiproofConeCanonical

theorem header {F C : Type} (c : Configuration F C)
    (a1 a2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdk c) a1 a2 saved f s)
    (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle (S2Z.Oracle.leadDigest (sdk c)) () H) :
    CPhy_Header.decode (bytesOf s.checkpoint.val) = some (H (bytesOf s.proof.val),H (bytesOf s.pub.val)) := by
  have accepted := cuts.second
  change VTop_Stages.verifier.candidate.tx2_authenticated (stage c) (digest c)
    s.pub s.proof s.checkpoint () none = ok (.Ok ()) at accepted
  obtain ⟨variant,shape,common⟩ := Tx2I_Cuts.authenticated_reached _ _ () s.pub s.proof s.checkpoint none accepted
  obtain ⟨p,a,g,geo,pending,out,after,flushed,back,v,read,_⟩ :=
    Tx2I_Cuts.common_reached _ _ () s.pub s.proof s.checkpoint none common
  have resumed := Port4A_ReaderInstall.accepted_source (AuS1_Install.base c.stageBase) c.reserved _ () s.checkpoint s.proof s.pub .S2 p a read
  exact CPhy_Header.reader c.reserved _ () H oracle s.checkpoint s.proof s.pub p a resumed

#print axioms header
end AspisR1.Hiq_DrvReaderHeader
end
