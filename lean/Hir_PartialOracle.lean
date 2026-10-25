import SdkC_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_PartialOracle
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- An explicit partial-syscall experiment. The fixed syscall failure schedule
is inspected before asking the ideal oracle. Successful replies come only from
that oracle. Failed attempts remain in Source.run's attempt log; they disclose
no digest and create no successful-read entry. This is a distinct experiment
from SdkC_Oracle.program, not a claimed replacement of its probability law. -/
def program (hashv : Parts → Result Digest) {A : Type} : Code A → Program Bytes State (Result A)
  | .done a => .done (.ok a)
  | .step r k => match r with
    | .ok a => program hashv (k a)
    | .fail e => .done (.fail e)
    | .div => .done .div
  | .read parts k => match hashv parts with
    | .ok _ => .ask (flatten parts) (fun d => program hashv (k (encodeState d)))
    | .fail e => .done (.fail e)
    | .div => .done .div

/-- Result and successful-read transport for EVERY source outcome, including
rejection after earlier reads, source panic and divergence. No success or
total-syscall hypothesis occurs. No probability transport is claimed. -/
theorem exact (hashv : Parts → Result Digest) (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    {A : Type} (code : Code A) (before : Log) :
    (eval H (program hashv code)).2 = (run hashv code before).1 ∧
      readLog (run hashv code before).2 = readLog before ++ (eval H (program hashv code)).1 := by
  induction code generalizing before with
  | done a => exact ⟨rfl,(List.append_nil _).symm⟩
  | step r k ih =>
    cases r with
    | ok a => exact ih a before
    | fail e => exact ⟨rfl,(List.append_nil _).symm⟩
    | div => exact ⟨rfl,(List.append_nil _).symm⟩
  | read parts k ih =>
    cases actual : hashv parts with
    | fail e => simp [program,run,actual,eval,readLog,SdkC_Oracle.readLog_append]
    | div => simp [program,run,actual,eval,readLog,SdkC_Oracle.readLog_append]
    | ok digest =>
      have decoded : decodeState digest = H (flatten parts) :=
        (syscall.returningValue parts digest actual).trans (p1.realization _)
      have encoded : encodeState (H (flatten parts)) = digest := by
        rw [← decoded]
        exact array_roundtrip digest
      obtain ⟨result,log⟩ := ih digest (before ++ [⟨parts,.ok digest⟩])
      simp only [program,run,actual,eval,encoded]
      refine ⟨result,?_⟩
      rw [log,SdkC_Oracle.readLog_append]
      simp only [readLog,List.filterMap_cons,List.filterMap_nil,List.append_nil]
      rw [decoded]
      simp only [List.append_assoc,List.singleton_append]

#print axioms exact
end AspisR1.Hir_PartialOracle
end
