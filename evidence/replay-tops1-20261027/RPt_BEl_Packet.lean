import RPt_BEl_ReachedReference
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_Packet
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_NativeConsolidation SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Derived source-cut/reference observation output. No accepted observation,
local Law or successful source log is an input field of this packet. -/
def Facts {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : Parts → Result Digest) (native : Bytes → State)
    (e1 e2 : Entry) (saved : alloc.vec.Vec U8) (post2 : Heap (Nat → Record)) : Prop :=
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
            (BEl_ReferenceSource.stageCode hashv s.proof p1 root1) before1.length before1).2.2

theorem of_native_acceptance {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (id : S2W_ExtractionBoundary.Program)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : Parts → Result Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (native : Bytes → State) (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (state1 state2 final1 final2 : A) (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : first native1 copy allocator e1 id data1 state1 = ok (.Ok (saved,post1,final1)))
    (accepted2 : second native2 allocator e2 id data2 slot state2 = ok (.Ok (post2,final2))) :
    Facts c hashv native e1 e2 saved post2 :=
  BEl_ReachedReference.cuts c copy std allocator e1 e2 id native1 native2 hashv extraction native syscall
    data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2

#print axioms of_native_acceptance
end AspisR1.BEl_Packet
end
