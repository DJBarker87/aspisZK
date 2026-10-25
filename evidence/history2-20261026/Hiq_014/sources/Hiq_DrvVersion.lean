import Hiq_CausalVersion
import Hiq_DrvShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_DrvVersion
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation S2W_EntryWriteHistory S2W_ReturnedCheckpoint

def version {A F C : Type} (c : Configuration F C)
    (keyLaw : (sdk c).op36 = Hist_Authority.keyEq)
    (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (initial final : Store) (l1 l2 : Layout)
    (data : Slice U8) (state final1 : A) (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record))
    (accepted : first native1 copy allocator (load initial l1) id data state = ok (.Ok (saved,post1,final1)))
    (events : List S2X.AccountEvent)
    (trace : Trace (sdk c) id (commit initial (l1.handles 2).1 saved) events final)
    (sameKey : (l2.handles 6).1 = (l1.handles 2).1)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdk c) (load initial l1).first ((load final l2).second secondSizes) saved f s) :
    S2X.CheckpointVersionBinding
      (payloadBytes encode
        (post1.payload ((load initial l1).heap.accounts 2).1) 1768)
      (bytesOf s.checkpoint.val) := by
  have native := (first_accepted native1 copy std allocator (load initial l1) id data state final1 saved post1 accepted).1
  have source := (extraction.stage1 id (load initial l1).first data).symm.trans native
  have shape := Hiq_DrvShape.on_cuts c (load initial l1) _ saved f s cuts owner ports
  let history := Hiq_CausalVersion.version (sdk c) keyLaw id initial final l1 l2 data saved source
    events trace sameKey shape.1 f s cuts
  have copied := Hist_CommittedPayload.copied _ native1 native2 hashv extraction copy std allocator
    (load initial l1) id data state final1 saved post1 accepted shape.2
  exact Hist_CommittedPayload.committed_version _ _ _ copied history

#print axioms version
end AspisR1.Hiq_DrvVersion
end
