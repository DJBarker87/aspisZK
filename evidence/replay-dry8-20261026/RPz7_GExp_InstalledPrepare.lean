import RPz7_GExp_PrepareAssociation
import RPz7_SdkD_PrepareTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_InstalledPrepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

def digest (sdk : AdapterRw.Ops) := AspisS6CurrentFirstInstallation.toDigest
  (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 sdk)

theorem associated (sdk : AdapterRw.Ops)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction sdk native1 native2 hashv)
    (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : AdapterRw.SolanaDigest)
    (input : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    SdkD_PrepareLower.Associated hashv
      (SdkD_PrepareSource.code ops B std (digest sdk) pub proof hash input) := by
  apply GExp_PrepareAssociation.prepare
  exact S2W_DigestExtraction.native_binding sdk native1 native2 hashv extraction

theorem erasure (sdk : AdapterRw.Ops)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction sdk native1 native2 hashv)
    (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : AdapterRw.SolanaDigest)
    (input : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) ()
      (SdkD_PrepareLower.lower (SdkD_PrepareSource.code ops B std (digest sdk) pub proof hash input)) =
    verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      (digest sdk) pub proof hash none input := by
  rw [SdkD_PrepareLower.erasure hashv _
    (associated sdk native1 native2 hashv extraction ops B std pub proof hash input)]
  exact SdkD_PrepareSource.source ops B std _ pub proof hash input

theorem accepted (sdk : AdapterRw.Ops)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction sdk native1 native2 hashv)
    (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : AdapterRw.SolanaDigest)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepared : verifier.Prepared)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (success : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      (digest sdk) pub proof hash none input = ok (.Ok prepared,scratch)) :
    eval H (SdkC_Oracle.program (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code ops B std (digest sdk) pub proof hash input))) =
    (SdkC_Source.readLog (SdkC_Source.run hashv (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code ops B std (digest sdk) pub proof hash input)) []).2,
      ok (.Ok prepared,scratch)) :=
  SdkD_PrepareTransport.accepted ops B std (digest sdk) pub proof hash input scratch prepared
    hashv sha256 H p1 syscall
    (associated sdk native1 native2 hashv extraction ops B std pub proof hash input) success

#print axioms associated
#print axioms erasure
#print axioms accepted
end AspisR1.GExp_InstalledPrepare
end
