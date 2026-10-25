import Hiq_DrvShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_DrvWriterHeader
open Aeneas Aeneas.Std Result S2W_NativeConsolidation S2W_D189Entry DrvC_Installation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep MultiproofConeCanonical

theorem header {F C : Type} (c : Configuration F C) (e1 : Entry)
    (a2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdk c) e1.first a2 saved f s)
    (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle (S2Z.Oracle.leadDigest (sdk c)) () H) :
    CPhy_Header.decode (bytesOf saved.val) = some (H (bytesOf f.proof.val),H (bytesOf f.pub.val)) := by
  have transformed := cuts
  rw [cphy_dictionary,Uni_Install.compose_tx1] at transformed
  obtain ⟨run,_,_,_,_,_,writer,_⟩ := WAdm_OriginalEndpoint.reached _ (Op5T_Concrete.current c.currentBase)
    c.reserved c.query c.geometry c.boundaries c.std e1 a2 saved f s transformed owner ports
  exact (CPhy_Header.writer _ () H oracle _ _ f.proof f.pub saved writer).1

#print axioms header
end AspisR1.Hiq_DrvWriterHeader
end
