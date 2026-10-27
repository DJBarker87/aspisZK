import RPz7_DrvC_Installation
import RPz7_SdkC_BatchPair
import Port4B_BatchJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEk_ReachedInputs
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_NativeConsolidation

/-- Actual accepted source call arguments on one fixed enclosing pair. This
extracts Prepared/root arrays, not a physical batch-state/recorder witness.
The original account records and allocator states remain fixed parameters. -/
theorem cuts {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (id : S2W_ExtractionBoundary.Program)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (state1 state2 final1 final2 : A) (saved : alloc.vec.Vec U8)
    (post1 post2 : Heap (Nat → Record))
    (accepted1 : first native1 copy allocator e1 id data1 state1 = ok (.Ok (saved,post1,final1)))
    (accepted2 : second native2 allocator e2 id data2 slot state2 = ok (.Ok (post2,final2))) :
    ∃ f s, SourceCuts (DrvC_Installation.sdk c) e1.first (e2.second secondSizes) saved f s ∧
      post2 = e2.heap ∧
      ∃ (p0 : AspisR1CurrentCaller.verifier.Prepared) (root0 : Array U8 32#usize)
        (p1 : VTop_Stages.verifier.Prepared) (root1 : Array U8 32#usize),
        Op5T_Install.currentBatch Port4B_Install.leaves (DrvC_Installation.currentDigest c)
          f.proof p0 root0 0#usize () = ok (.Ok ()) ∧
        Op5T_Install.stageBatch Port4B_Install.leaves (DrvC_Installation.digest c)
          s.proof p1 root1 1#usize () = ok (.Ok ()) := by
  obtain ⟨owned1,_⟩ := first_accepted native1 copy std allocator e1 id data1 state1 final1 saved post1 accepted1
  obtain ⟨owned2,frame⟩ := second_accepted native2 allocator e2 id data2 slot state2 final2 post2 accepted2
  obtain ⟨f,s,pair⟩ := cuts_of_acceptance _ native1 native2 hashv
    (S2W_DigestExtraction.sourceBoundary _ native1 native2 hashv extraction)
    id e1.first (e2.second secondSizes) data1 data2 slot saved owned1 owned2
  refine ⟨f,s,pair,frame,?_⟩
  have selected := pair
  rw [DrvC_Installation.aus1_dictionary] at selected
  have batches := Op5T_SamePair.batches c.adapter
    (Uni_Install.base c.currentBase c.reserved c.query c.geometry)
    (SdkD_Install.stage c.stageBase c.reserved c.query c.geometry)
    c.finish c.boundaries c.std _ _ saved f s selected
  simpa only [DrvC_Installation.currentDigest,DrvC_Installation.digest,
    DrvC_Installation.aus1_dictionary,SdkD_PairBatches.dictionary] using batches

#print axioms cuts
end AspisR1.BEk_ReachedInputs
end
