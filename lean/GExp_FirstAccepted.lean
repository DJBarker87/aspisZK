import GExp_FirstSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_FirstAccepted
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw

def program (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) :=
  SdkC_Oracle.program (GExp_FirstCode.code base B std hashv D semantic pub proof split)

theorem accepted (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit) (law : ∀ parts, D.digest () parts = hashv parts)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (success : verifier.candidate.tx1 (GExp_FirstCode.installed base B std)
      D semantic pub proof split () none = ok (.Ok saved)) :
    eval H (program base B std hashv D semantic pub proof split) =
      (SdkC_Source.readLog (SdkC_Source.run hashv
        (GExp_FirstCode.code base B std hashv D semantic pub proof split) []).2,ok (.Ok saved)) := by
  apply SdkC_Oracle.accepted_exact hashv sha256 H p1 syscall
  exact (SdkC_Source.erasure hashv _ []).trans
    ((GExp_FirstSource.source base B std hashv D law semantic pub proof split).trans success)

#print axioms accepted
end AspisR1.GExp_FirstAccepted
end
