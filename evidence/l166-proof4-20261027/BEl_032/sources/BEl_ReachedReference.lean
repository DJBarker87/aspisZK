import BEl_SlotObservation
import BEk_ReachedInputs
import P6C_OnCuts
import BEf_Count
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_ReachedReference
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_NativeConsolidation SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem cuts {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (id : S2W_ExtractionBoundary.Program)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : Parts → Result Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (native : Bytes → State) (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (state1 state2 final1 final2 : A) (saved : alloc.vec.Vec U8)
    (post1 post2 : Heap (Nat → Record))
    (accepted1 : first native1 copy allocator e1 id data1 state1 = ok (.Ok (saved,post1,final1)))
    (accepted2 : second native2 allocator e2 id data2 slot state2 = ok (.Ok (post2,final2))) :
    ∃ f s, SourceCuts (DrvC_Installation.sdk c) e1.first (e2.second secondSizes) saved f s ∧
      post2=e2.heap ∧
      ∃ (p0 : AspisR1CurrentCaller.verifier.Prepared) (root0 : Digest)
        (p1 : VTop_Stages.verifier.Prepared) (root1 : Digest),
        SdkC_BatchPair.Returning hashv native (SdkC_BatchSource.currentCode hashv f.proof p0 root0) (.Ok ()) ∧
        SdkC_BatchPair.Returning hashv native (SdkC_BatchSource.stageCode hashv s.proof p1 root1) (.Ok ()) ∧
        ∀ before0 before1 : Log,
          BEj_SlotExport.Prefix hashv native (SdkC_BatchSource.currentCode hashv f.proof p0 root0) before0
            (BEl_SlotObservation.observe (BEf_Count.call hashv)
              (BEl_ReferenceSource.currentCode hashv f.proof p0 root0) before0.length before0).2.2 ∧
          BEj_SlotExport.Prefix hashv native (SdkC_BatchSource.stageCode hashv s.proof p1 root1) before1
            (BEl_SlotObservation.observe (BEf_Count.call hashv)
              (BEl_ReferenceSource.stageCode hashv s.proof p1 root1) before1.length before1).2.2 := by
  obtain ⟨f,s,sourceCuts,frame,_⟩ := BEk_ReachedInputs.cuts c copy std allocator e1 e2 id
    native1 native2 hashv extraction data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2
  have identity : S2W_ExtractionBoundary.P1 native native := ⟨fun _ => rfl⟩
  obtain ⟨p0,root0,p1,root1,safe0,safe1,_⟩ := P6C_OnCuts.same_cuts c native1 native2 hashv extraction
    native native identity syscall e1.first (e2.second secondSizes) saved f s sourceCuts
  refine ⟨f,s,sourceCuts,frame,p0,root0,p1,root1,safe0.1,safe1.1,?_⟩
  intro before0 before1
  exact ⟨BEl_SlotObservation.current_prefix (BEf_Count.call hashv) hashv (fun _ _ => rfl)
      native f.proof p0 root0 before0.length before0 safe0.1,
    BEl_SlotObservation.stage_prefix (BEf_Count.call hashv) hashv (fun _ _ => rfl)
      native s.proof p1 root1 before1.length before1 safe1.1⟩

#print axioms cuts
end AspisR1.BEl_ReachedReference
end
