import Hiq_NativeHistory
import Hiq_FirstShape
import Hiq_CausalVersion
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_NativeVersion
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry S2Trust S2W_D189Entry S2W_D189Wrappers
open DrvC_Installation S2W_NativeConsolidation MultiproofConeCanonical
open S2W_EntryWriteHistory S2W_ReturnedCheckpoint
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def version {A F C : Type} (c : Configuration F C)
    (law : (sdk c).op36 = Hist_Authority.keyEq)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (trustedCopy : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (initial : Store) (l1 l2 : Layout) (data : Slice U8) (state final1 : A)
    (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record))
    (accepted : first native1 copy allocator (load initial l1) id data state = ok (.Ok (saved,post1,final1)))
    (actions : List (Hiq_NativeAction.Action A)) (sameKey : (l2.handles 6).1 = (l1.handles 2).1)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdk c) (load initial l1).first
      ((load (Hiq_NativeHistory.run native1 copy allocator id (commit initial (l1.handles 2).1 saved) actions).1 l2).second secondSizes)
        saved f s) :
    S2X.CheckpointVersionBinding (payloadBytes encode (post1.payload ((load initial l1).heap.accounts 2).1) 1768)
      (bytesOf s.checkpoint.val) := by
  have native := (first_accepted native1 copy trustedCopy allocator (load initial l1) id data state final1 saved post1 accepted).1
  have source := (extraction.stage1 id (load initial l1).first data).symm.trans native
  have shape := Hiq_FirstShape.source c id _ data saved source
  let history := Hiq_CausalVersion.version (sdk c) law id initial _ l1 l2 data saved source _
    (Hiq_NativeHistory.classified native1 copy allocator id (sdk c) law extraction.stage1 trustedCopy _ actions)
    sameKey shape.1 f s cuts
  have copied := Hist_CommittedPayload.copied _ native1 native2 hashv extraction copy trustedCopy allocator
    (load initial l1) id data state final1 saved post1 accepted shape.2
  exact Hist_CommittedPayload.committed_version _ _ _ copied history

#print axioms version
end AspisR1.Hiq_NativeVersion
end
