import BEn_LocalAssociation
import BEk_ReachedInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEn_ReachedLaws
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_NativeConsolidation SdkC_Source
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
      ∃ (p0 : AspisR1CurrentCaller.verifier.Prepared) (root0 : Digest)
        (p1 : VTop_Stages.verifier.Prepared) (root1 : Digest),
        Op5T_Install.currentBatch Port4B_Install.leaves (DrvC_Installation.currentDigest c)
          f.proof p0 root0 0#usize () = ok (.Ok ()) ∧
        Op5T_Install.stageBatch Port4B_Install.leaves (DrvC_Installation.digest c)
          s.proof p1 root1 1#usize () = ok (.Ok ()) ∧
        ∀ (S : Type) (call : Parts → S → Result Digest × S) (state : S) (before : Log),
          BEh_Scope.Law
            (BEn_ExtractedSlots.observe call (BEn_ExtractedSlots.currentBody hashv f.proof p0 root0) state before)
            (BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv f.proof p0 root0) state before) ∧
          BEh_Scope.Law
            (BEn_ExtractedSlots.observe call (BEn_ExtractedSlots.stageBody hashv s.proof p1 root1) state before)
            (BEf_Carrier.run call (SdkC_BatchSource.stageCode hashv s.proof p1 root1) state before) := by
  obtain ⟨f,s,cuts,frame,p0,root0,p1,root1,first,second⟩ :=
    BEk_ReachedInputs.cuts c copy std allocator e1 e2 id native1 native2 hashv extraction
      data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2
  exact ⟨f,s,cuts,frame,p0,root0,p1,root1,first,second,
    fun S call state before => ⟨BEn_LocalAssociation.current call hashv f.proof p0 root0 state before,
      BEn_LocalAssociation.stage call hashv s.proof p1 root1 state before⟩⟩

#print axioms cuts
end AspisR1.BEn_ReachedLaws
end
