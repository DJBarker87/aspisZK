import DrvC_SourceEntry
import GExp_PrepareTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_AuS1
open Aeneas Aeneas.Std Result
open DrvC_Installation Tx1Q_Carriers DrvC_OraclePort
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem preparation_program {F C : Type} (c : Configuration F C)
    (semantic : Port1_Driver.Semantic) (proof : Slice U8) (input : Array Tx1Q_Carriers.C.E 29#usize) :
    DrvC_Implementation.implementation c
      (.op7 (digest c) semantic proof () none (arr e input)) =
      mapR DrvC_Dictionary.prepareReply
        (AspisR1PublicPreparation.PreparedHashCode.oracleProgram
          (SdkD_PrepareSource.code (current c) c.boundaries c.std (currentDigest c)
            (AspisS6CurrentVerifierCarrier.toPublic semantic) proof () input)) := by
  rw [← DrvC_CallCode.implementation]
  change SdkC_Oracle.program (DrvC_Implementation.prepare c (digest c) semantic proof () (arr e input)) = _
  dsimp only [DrvC_Implementation.prepare]
  rw [DrvC_CurrentSlots.arr_roundtrip e unE unE_e,DrvC_Program.program_map,SdkD_PrepareLower.program]
  rfl

theorem preparation_trace {F C : Type} (c : Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (semantic : Port1_Driver.Semantic) (proof : Slice U8)
    (input scratch : Array Tx1Q_Carriers.C.E 29#usize) (p : Tx1Q_Carriers.C.P)
    (accepted : AspisR1CurrentCaller.verifier.candidate.prepare (currentInstalled c) (currentDigest c)
      (AspisS6CurrentVerifierCarrier.toPublic semantic) proof () none input = ok (.Ok p,scratch)) :
    (eval H (DrvC_Implementation.implementation c
      (.op7 (digest c) semantic proof () none (arr e input)))).1 =
      AuS1_Recovery.log (current c) c.boundaries c.std (currentDigest c)
        (AspisS6CurrentVerifierCarrier.toPublic semantic) proof () input := by
  have value := GExp_InstalledPrepare.accepted (sdk c) native1 native2 hashv extraction
    (current c) c.boundaries c.std (AspisS6CurrentVerifierCarrier.toPublic semantic) proof () input scratch p
    sha256 H p1 syscall accepted
  have trace := congrArg Prod.fst value
  rw [GExp_PrepareTrace.source_log (sdk c) native1 native2 hashv extraction] at trace
  rw [preparation_program]
  unfold mapR
  rw [DrvC_Program.eval_map,← SdkD_PrepareLower.program]
  exact trace

#print axioms preparation_program
#print axioms preparation_trace
end AspisR1.DrvC_AuS1
end
