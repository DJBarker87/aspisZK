import GExp_PartialCount
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_ReadPrefix
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

theorem retained_reads {A : Type} (code : Code A)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) (before : SdkC_Source.Log) :
    ∃ kept remaining : List (Bytes × State),
      SdkC_Source.readLog (SdkC_Source.run hashv code before).2 = SdkC_Source.readLog before ++ kept ∧
      (eval H (SdkC_Oracle.program code)).1 = kept ++ remaining := by
  induction code generalizing before with
  | done a => exact ⟨[],[],(List.append_nil _).symm,rfl⟩
  | step r k ih => cases r with
    | ok a => exact ih a before
    | fail e => exact ⟨[],[],(List.append_nil _).symm,rfl⟩
    | div => exact ⟨[],[],(List.append_nil _).symm,rfl⟩
  | read parts k ih =>
    cases actual : hashv parts with
    | ok digest =>
      have decoded : decodeState digest = H (flatten parts) :=
        (syscall.returningValue parts digest actual).trans (p1.realization _)
      have encoded : encodeState (H (flatten parts)) = digest := by
        rw [← decoded];exact array_roundtrip digest
      obtain ⟨kept,remaining,native,ideal⟩ := ih digest (before ++ [⟨parts,.ok digest⟩])
      refine ⟨(flatten parts,H (flatten parts))::kept,remaining,?_,?_⟩
      · simp only [SdkC_Source.run,actual]
        rw [native,SdkC_Oracle.readLog_append]
        simp only [SdkC_Source.readLog,
          List.filterMap_cons,List.filterMap_nil,List.append_nil,decoded,List.append_assoc,List.singleton_append]
      · simp only [SdkC_Oracle.program,eval,encoded,ideal,List.cons_append]
    | fail e =>
      refine ⟨[],(eval H (SdkC_Oracle.program (.read parts k))).1,?_,rfl⟩
      simp only [SdkC_Source.run,actual,SdkC_Oracle.readLog_append,SdkC_Source.readLog,
        List.filterMap_append,List.filterMap_cons,List.filterMap_nil,List.append_nil]
    | div =>
      refine ⟨[],(eval H (SdkC_Oracle.program (.read parts k))).1,?_,rfl⟩
      simp only [SdkC_Source.run,actual,SdkC_Oracle.readLog_append,SdkC_Source.readLog,
        List.filterMap_append,List.filterMap_cons,List.filterMap_nil,List.append_nil]

#print axioms retained_reads
end AspisR1.GExp_ReadPrefix
end
