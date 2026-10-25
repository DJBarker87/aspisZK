import AuS1_Prepare
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Transport
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Complete concrete preparation transport with partial syscalls. The local
structural association is derived rather than supplied as a premise. -/
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
    (source : ∀ h parts, D.digest h parts = hashv parts)
    (success : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      D pub proof hash none input = ok (.Ok prepared,scratch)) :
    eval H (SdkC_Oracle.program (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code ops B std D pub proof hash input))) =
      (SdkC_Source.readLog (SdkC_Source.run hashv (SdkD_PrepareLower.lower
        (SdkD_PrepareSource.code ops B std D pub proof hash input)) []).2,
        ok (.Ok prepared,scratch)) := by
  exact SdkD_PrepareTransport.accepted ops B std D pub proof hash input scratch prepared
    hashv sha256 H p1 syscall
    (AuS1_Prepare.associated ops B std D hashv source pub proof hash input) success

#print axioms accepted
end AspisR1.AuS1_Transport
end
