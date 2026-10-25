import Hir_ReaderMarker
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_InstalledReader
open Aeneas Aeneas.Std Result

theorem marker {F C : Type} (c : DrvC_Installation.Configuration F C)
    (pub proof ck : Slice U8)
    (accepted : (DrvC_Installation.sdk c).op11
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (DrvC_Installation.sdk c))
      pub proof ck () none = ok (.Ok ())) : Hist_Store.Initialized ck := by
  let D := AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (DrvC_Installation.sdk c)
  have actual : VTop_Stages.verifier.candidate.tx2_authenticated (DrvC_Installation.stage c)
      D pub proof ck () none = ok (.Ok ()) := accepted
  obtain ⟨variant,shape,common⟩ := Tx2I_Cuts.authenticated_reached _ D () pub proof ck none actual
  obtain ⟨p,a,g,geometry,pending,returned,after,flushed,back,v,resume,rest⟩ :=
    Tx2I_Cuts.common_reached _ D () pub proof ck none common
  have reader := Tx2N_Install.reader_success (AuS1_Install.base c.stageBase) c.reserved c.query
    D () ck proof pub .S2 p a resume
  exact Hir_ReaderMarker.resume c.reserved (VTop_Checkpoint.digest D) ck proof pub () p a reader

#print axioms marker
end AspisR1.Hir_InstalledReader
end
