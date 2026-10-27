import RPz7_CPP_Compatibility
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_OracleSource
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation CPP_Oracle
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store) (input : Invocation A)

theorem invalid (H : Bytes → State) (bad : ¬ compatible input) :
    eval H (CPP_Oracle.program c hashv copy allocator id store input) =
      ([],(store,.rollback,rejectedReply input)) := by
  simp only [CPP_Oracle.program,if_neg bad,eval]

theorem valid (H : Bytes → State) (good : compatible input) :
    eval H (CPP_Oracle.program c hashv copy allocator id store input) =
      eval H (Hir_Call.oracle c hashv copy allocator id store input.call) := by
  simp only [CPP_Oracle.program,if_pos good]

theorem effect (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    (eval H (CPP_Oracle.program c hashv copy allocator id store input)).2 =
      CPP_Invocation.native n1 n2 copy allocator id store input := by
  by_cases good : compatible input
  · rw [valid c hashv copy allocator id store input H good,
      Hir_CallSource.effect c hashv copy allocator id n1 n2 extraction sha256 H p1 syscall,
      CPP_Compatibility.valid n1 n2 copy allocator id store input good]
  · rw [invalid c hashv copy allocator id store input H good,
      CPP_Compatibility.invalid n1 n2 copy allocator id store input good]

#print axioms invalid
#print axioms valid
#print axioms effect
end AspisR1.CPP_OracleSource
end
