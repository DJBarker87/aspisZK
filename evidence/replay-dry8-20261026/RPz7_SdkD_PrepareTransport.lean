import RPz7_SdkD_PrepareSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_PrepareTransport
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- LOCAL bridge only. The structural association argument is explicitly
unproved for the complete concrete preparation tree; it is not inserted into
SdkD_Accepted or counted as removal of authenticated_S1. Native syscall
totality is not required, and the log retains ordered duplicate reads. -/
theorem accepted (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : Hash)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepared : verifier.Prepared)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (association : SdkD_PrepareLower.Associated hashv
      (SdkD_PrepareSource.code ops B std D pub proof hash input))
    (success : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      D pub proof hash none input = ok (.Ok prepared,scratch)) :
    eval H (SdkC_Oracle.program (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code ops B std D pub proof hash input))) =
      (SdkC_Source.readLog (SdkC_Source.run hashv (SdkD_PrepareLower.lower
        (SdkD_PrepareSource.code ops B std D pub proof hash input)) []).2,
        ok (.Ok prepared,scratch)) := by
  have native : (SdkC_Source.run hashv (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code ops B std D pub proof hash input)) []).1 =
      ok (.Ok prepared,scratch) := by
    rw [SdkC_Source.erasure,SdkD_PrepareLower.erasure hashv _ association,
      SdkD_PrepareSource.source]
    exact success
  exact SdkC_Oracle.accepted_exact hashv sha256 H p1 syscall _ _ native

#print axioms accepted
end AspisR1.SdkD_PrepareTransport
end
