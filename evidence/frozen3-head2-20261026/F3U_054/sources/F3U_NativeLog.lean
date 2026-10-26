import F3U_PairLog
import F3S_NativeChildren
import F3S_SdkDictionary
import RawJ_OriginalAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_NativeLog
open Aeneas Aeneas.Std Result
open DrvC_Installation S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem same {F C : Type} (c : Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 id accounts1 data1=ok (.Ok saved))
    (accepted2 : native2 id accounts2 data2 slot=ok (.Ok ()))
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (f : FirstCut) (s : SecondCut) (log : S2W_Trace.Log)
    (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s)
    (recorded : RawJ_RecordCuts.Recorded f s saved log)
    (ran : S2W_Trace.run (sdk c) (S2W_Observation.two (sdk c)
      id accounts1 data1 accounts2 data2 slot) []=ok (.Ok saved,log))
    (proof : bytesOf s.proof.val=bytesOf f.proof.val) (pub : bytesOf s.pub.val=bytesOf f.pub.val)
    (checkpoint : bytesOf s.checkpoint.val=bytesOf saved.val) :
    (eval H (DrvC_PairProgram.source c hashv f.semantic f.pub f.proof)).1=
      (eval H (GExq_CallerRecord.program c.adapter c.currentBase (AuS1_Install.base c.stageBase)
        c.finish c.reserved c.query c.geometry c.boundaries c.std hashv
        id accounts1 accounts2 data1 data2 slot)).1 := by
  have law := S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction
  have children := F3S_NativeChildren.on_pair c.adapter c.currentBase (AuS1_Install.base c.stageBase)
    c.finish c.reserved c.query c.geometry c.boundaries c.std hashv law
    native1 native2 extraction id accounts1 accounts2 data1 data2 slot saved accepted1 accepted2
    f s log ran recorded
  have original := RawJ_OriginalAccepted.accepted c.adapter c.currentBase (AuS1_Install.base c.stageBase)
    c.finish c.reserved c.query c.geometry c.boundaries c.std hashv law sha256 H p1 syscall
    id accounts1 accounts2 data1 data2 slot saved f s log ran recorded
  have pair := congrArg Prod.fst (F3U_PairLog.evaluated c native1 native2 hashv extraction sha256 H p1 syscall
    accounts1 accounts2 saved f s cuts proof pub checkpoint)
  rw [congrArg Prod.fst original,children]
  rw [F3U_FirstCode.same,F3U_SecondCode.same]
  exact pair

#print axioms same
end AspisR1.F3U_NativeLog
end
