import CPR_CommittedLoad
import Hiq_FirstShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPR_WriterLoad
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState CPR_Persistence
open S2W_NativeConsolidation MultiproofConeCanonical
open S2W_EntryWriteHistory S2W_ReturnedCheckpoint

def on_cuts {A F C Tx Key : Type} (c : DrvC_Installation.Configuration F C)
    (keyLaw : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (initial : Bank) (layout1 : Layout) (e1 e2 : Entry)
    (entry1 : e1 = load initial.cells layout1)
    (data1 : Slice U8) (state1 final1 : A) (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record))
    (accepted1 : first n1 copy allocator e1 id data1 state1 = ok (.Ok (saved,post1,final1)))
    (actions : List (Action A)) (positive : 0 < initial.lamports (layout1.handles 2).1)
    (next : Tx → Tx → Prop) (ordinary : Tx → Key → Prop)
    (before tentative : Tx → Key → Image) (success : Tx → Bool)
    (loaded : Tx → Key → Option Image)
    (law : TwoTransactionLaw next ordinary before tentative success loaded)
    (t u : Tx) (physicalKey : Key) (adjacent : next t u) (eligible : ordinary t physicalKey)
    (tentativeView : tentative t physicalKey = snapshot
      (CPP_BankHistory.run n1 n2 copy allocator id
        (CPR_SourceBank.afterCopy initial (layout1.handles 2).1 saved) actions).1 (layout1.handles 2).1)
    (status : success t = true)
    (entry2View : ∀ image, loaded u physicalKey = some image →
      (e2.buffers (e2.handles 6).1).val = image.cell.data.val)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (DrvC_Installation.sdk c) e1.first (e2.second secondSizes) saved f s) :
    S2X.CheckpointVersionBinding
      (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768)
      (bytesOf s.checkpoint.val) := by
  have native := (S2W_D189Wrappers.first_accepted n1 copy std allocator e1 id data1 state1 final1 saved post1 accepted1).1
  have sourceAccepted := (extraction.stage1 id e1.first data1).symm.trans native
  have shape := Hiq_FirstShape.source c id e1.first data1 saved sourceAccepted
  have owner := CPR_SourceBank.copied_owner (DrvC_Installation.sdk c) keyLaw id initial layout1 data1 saved
    (by rw [← entry1]; exact sourceAccepted)
  have marker := CPR_SourceBank.copied_marker initial (layout1.handles 2).1 saved shape.1
  let history := CPR_CommittedLoad.binding (DrvC_Installation.sdk c) keyLaw n1 n2
    (fun id accounts data => (extraction.stage1 id accounts data).symm)
    copy std allocator id (CPR_SourceBank.afterCopy initial (layout1.handles 2).1 saved) actions
    (layout1.handles 2).1 owner marker positive next ordinary before tentative success loaded law
    t u physicalKey adjacent eligible tentativeView status e2 entry2View
  let version := CPR_SourceBank.on_cuts (DrvC_Installation.sdk c) e1 e2 saved f s cuts initial (layout1.handles 2).1 history
  have copied := Hist_CommittedPayload.copied (DrvC_Installation.sdk c) n1 n2 hashv extraction copy std allocator
    e1 id data1 state1 final1 saved post1 accepted1 shape.2
  exact Hist_CommittedPayload.committed_version _ _ _ copied version

#print axioms on_cuts
end AspisR1.CPR_WriterLoad
end
