import SdkC_SourceLaws
import MultiproofConePhysicalTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkC_Oracle
open Aeneas Aeneas.Std Result
open SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Ideal execution of the same literal source syntax. No log is an input. -/
def program {A : Type} : Code A → Program Bytes State (Result A)
  | .done a => .done (.ok a)
  | .step r k => match r with
    | .ok a => program (k a)
    | .fail e => .done (.fail e)
    | .div => .done .div
  | .read parts k => .ask (flatten parts) (fun d => program (k (encodeState d)))

theorem readLog_append (left right : Log) :
    readLog (left ++ right) = readLog left ++ readLog right := by
  exact List.filterMap_append

/-- The real accepted source execution and ideal program have EXACT ordered
successful reads, with duplicates retained. Rejected source calls are not
silently given a fictitious successful continuation. -/
theorem accepted_transport (hashv : Parts → Result Digest) (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    {A : Type} (code : Code A) (before : Log) (value : A)
    (accepted : (run hashv code before).1 = .ok value) :
    (eval H (program code)).2 = .ok value ∧
      readLog (run hashv code before).2 = readLog before ++ (eval H (program code)).1 := by
  induction code generalizing before with
  | done a =>
    exact ⟨accepted,(List.append_nil _).symm⟩
  | step r k ih =>
    cases r with
    | fail e => cases accepted
    | div => cases accepted
    | ok a => exact ih a before accepted
  | read parts k ih =>
    cases actual : hashv parts with
    | fail e => simp only [run,actual] at accepted; cases accepted
    | div => simp only [run,actual] at accepted; cases accepted
    | ok digest =>
      simp only [run,actual] at accepted ⊢
      have decoded : decodeState digest = H (flatten parts) :=
        (syscall.returningValue parts digest actual).trans (p1.realization _)
      have encoded : encodeState (H (flatten parts)) = digest := by
        rw [← decoded]
        exact array_roundtrip digest
      obtain ⟨result,log⟩ := ih digest (before ++ [⟨parts,.ok digest⟩]) accepted
      simp only [program,eval,encoded]
      refine ⟨result,?_⟩
      rw [log,readLog_append]
      simp only [readLog,List.filterMap_cons,List.filterMap_nil,List.append_nil]
      rw [decoded]
      simp only [List.append_assoc,List.singleton_append]

/-- Exact result-and-log equality on the accepted source class. -/
theorem accepted_exact (hashv : Parts → Result Digest) (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    {A : Type} (code : Code A) (value : A)
    (accepted : (run hashv code []).1 = .ok value) :
    eval H (program code) = (readLog (run hashv code []).2,.ok value) := by
  obtain ⟨result,log⟩ := accepted_transport hashv sha256 H p1 syscall code [] value accepted
  apply Prod.ext
  · simpa only [readLog,List.filterMap_nil,List.nil_append] using log.symm
  · exact result

#print axioms readLog_append
#print axioms accepted_transport
#print axioms accepted_exact
end AspisR1.SdkC_Oracle
end
