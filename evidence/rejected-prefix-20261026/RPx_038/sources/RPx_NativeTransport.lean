import RPx_InstalledBudget
import RPx_AttemptPrefix
import DrvC_Installation
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_NativeTransport
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

def PrefixBound {T : Type} (code : CheckpointBytes5Effect.Code T) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (H : Bytes → State) (n : Nat) : Prop :=
  (SdkC_Source.run hashv code []).2.length≤n ∧
  ∃ kept remaining : List Bytes,
    RPx_AttemptPrefix.addresses (SdkC_Source.run hashv code []).2=kept ∧
    (eval H (SdkC_Oracle.program code)).1.map Prod.fst=kept++remaining

theorem bounded {T : Type} (code : CheckpointBytes5Effect.Code T) (n : Nat)
    (count : GExp_CountLaws.count n code)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) : PrefixBound code hashv H n := by
  refine ⟨?_,?_⟩
  · exact GExp_PartialCount.from_count code n count hashv sha256 H p1 syscall []
  · simpa only [RPx_AttemptPrefix.addresses,List.map_nil,List.nil_append] using
      RPx_AttemptPrefix.transport code hashv sha256 H p1 syscall []

def firstCode {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program) (data : Slice U8) (state : A) :=
  GExq_InstalledWrapper.first c.adapter c.currentBase (AuS1_Install.base c.stageBase) c.finish
    c.reserved c.query c.geometry c.boundaries c.std hashv copy allocator e id data state

def secondCode {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program) (data : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state : A) :=
  GExq_InstalledWrapper.second c.adapter c.currentBase (AuS1_Install.base c.stageBase) c.finish
    c.reserved c.query c.geometry c.boundaries c.std hashv allocator e id data slot state

theorem first {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program) (data : Slice U8) (state : A)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    let code := firstCode c hashv copy allocator e id data state
    (SdkC_Source.run hashv code []).1=S2W_D189Wrappers.first native1 copy allocator e id data state ∧
    PrefixBound code hashv H 1018 := by
  dsimp only
  constructor
  · exact (SdkC_Source.erasure hashv _ []).trans
      (GExq_InstalledWrapper.first_source _ _ _ _ _ _ _ _ _ hashv
        copy allocator e id data state native1 native2 extraction)
  · apply bounded _ 1018 _ hashv sha256 H p1 syscall
    exact RPx_InstalledBudget.first _ _ _ _ _ _ _ _ _ hashv copy allocator e id data state

theorem second {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program) (data : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state : A)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    let code := secondCode c hashv allocator e id data slot state
    (SdkC_Source.run hashv code []).1=S2W_D189Wrappers.second native2 allocator e id data slot state ∧
    PrefixBound code hashv H 903 := by
  dsimp only
  constructor
  · exact (SdkC_Source.erasure hashv _ []).trans
      (GExq_InstalledWrapper.second_source _ _ _ _ _ _ _ _ _ hashv
        allocator e id data slot state native1 native2 extraction)
  · apply bounded _ 903 _ hashv sha256 H p1 syscall
    exact RPx_InstalledBudget.second _ _ _ _ _ _ _ _ _ hashv allocator e id data slot state

#print axioms bounded
#print axioms first
#print axioms second
end AspisR1.RPx_NativeTransport
end
