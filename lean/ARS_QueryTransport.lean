import ARR_ReturnCoverage
import P6C_Accepted
import OracleProgramReplay
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_QueryTransport
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

/-- Agreement is required only at successful calls actually made by this run.
There is deliberately no requirement on an unissued address. -/
def Agrees (H : Bytes → State) (log : Log) : Prop :=
  ∀ q ∈ log, ∀ digest, q.returned = ok digest →
    decodeState digest = H (flatten q.parts)

/-- Exact transport includes pure source rejection and all duplicate calls.
The separate returns certificate excludes syscall failures, not pure errors. -/
theorem covered {A : Type} (hashv : Parts → Result Digest)
    (H : Bytes → State) (code : Code A) (before : Log)
    (returns : ARR_ReturnCoverage.ReturnsOnly (run hashv code before).2)
    (agrees : Agrees H (run hashv code before).2) :
    ARR_OracleCoverage.Covered H hashv code := by
  induction code generalizing before with
  | done value => trivial
  | step result next ih =>
    cases result with
    | ok value => exact ih value before returns agrees
    | fail error => trivial
    | div => trivial
  | read parts next ih =>
    have member : (⟨parts,hashv parts⟩ : Query) ∈
        (run hashv (.read parts next) before).2 := by
      cases answer : hashv parts with
      | fail error => simp only [run,answer]; exact List.mem_append_right _ (List.mem_singleton_self _)
      | div => simp only [run,answer]; exact List.mem_append_right _ (List.mem_singleton_self _)
      | ok digest =>
        simp only [run,answer]
        obtain ⟨suffix,layout⟩ := prefix_preserved hashv (next digest) (before ++ [⟨parts,ok digest⟩])
        rw [layout]
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨digest,actual⟩ := returns _ member
    have answer : hashv parts = ok digest := actual
    have decoded := agrees _ member digest actual
    have encoded : encodeState (H (flatten parts)) = digest := by
      rw [← decoded]
      exact array_roundtrip digest
    refine ⟨answer.trans (congrArg Result.ok encoded.symm),?_⟩
    rw [encoded]
    exact ih digest (before ++ [⟨parts,ok digest⟩])
      (by simpa only [run,answer] using returns)
      (by simpa only [run,answer] using agrees)

/-- On every query-consistent world, preserve the literal result, chronological
successful log and attempted-address log, including rejection prefixes. -/
theorem exact {A : Type} (hashv : Parts → Result Digest)
    (H : Bytes → State) (code : Code A)
    (returns : ARR_ReturnCoverage.ReturnsOnly (run hashv code []).2)
    (agrees : Agrees H (run hashv code []).2) :
    (run hashv code []).1 = (eval H (SdkC_Oracle.program code)).2 ∧
    readLog (run hashv code []).2 = (eval H (SdkC_Oracle.program code)).1 ∧
    RPx_AttemptPrefix.addresses (run hashv code []).2 =
      (eval H (SdkC_Oracle.program code)).1.map Prod.fst := by
  simpa only [readLog,List.filterMap_nil,RPx_AttemptPrefix.addresses,List.map_nil,List.nil_append]
    using ARR_OracleCoverage.exact H hashv code (covered hashv H code [] returns agrees) []

/-- Native acceptance supplies the returns certificate, never an all-world
native/syscall factory. A new H only needs the issued-address agreement. -/
theorem accepted {A : Type} (hashv : Parts → Result Digest)
    (H : Bytes → State) (code : Code A) (value : A)
    (success : (run hashv code []).1 = ok value)
    (agrees : Agrees H (run hashv code []).2) :
    eval H (SdkC_Oracle.program code) = (readLog (run hashv code []).2,ok value) := by
  have returns := P6C_Accepted.issued_calls_ok hashv code [] value success (by simp)
  obtain ⟨result,reads,_⟩ := exact hashv H code returns agrees
  exact Prod.ext reads.symm (result.symm.trans success)

#print axioms covered
#print axioms exact
#print axioms accepted
end AspisR1.ARS_QueryTransport
end
