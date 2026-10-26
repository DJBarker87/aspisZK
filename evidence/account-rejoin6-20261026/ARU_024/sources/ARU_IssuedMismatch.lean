import ARU_FiniteIssued
import ART_QueryCylinder
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_IssuedMismatch
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

/-- This concerns an ISSUED address. It does not repeat the old NativeAt
unissued-address obstruction: the new local interface correctly rejects it. -/
theorem excluded (native : Bytes → State) (log : Log)
    (original : ARS_QueryTransport.Agrees native log)
    (q : Query) (member : q ∈ log) (digest : Digest) (returned : q.returned = ok digest)
    (value : State) (different : value ≠ native (flatten q.parts)) :
    ¬ ARS_QueryTransport.Agrees (ART_QueryCylinder.change native (flatten q.parts) value) log := by
  intro compatible
  have old := original q member digest returned
  have changed := compatible q member digest returned
  simp only [ART_QueryCylinder.change,if_pos rfl] at changed
  exact different (changed.symm.trans old)

/-- Small literal source counterexample to a universal accepted-world native
factory with a FIXED hashv. All ideal worlds accept this digest-returning code,
while native execution returns one fixed digest. This is not a real-byte R1
fixture or an attack; it isolates what a different-execution factory must do. -/
theorem different_execution (hashv : Parts → Result Digest) (parts : Parts) (digest : Digest)
    (returned : hashv parts = ok digest) (H : Bytes → State)
    (different : H (flatten parts) ≠ decodeState digest) :
    (eval H (SdkC_Oracle.program (digestCode parts))).2 = ok (encodeState (H (flatten parts))) ∧
    (run hashv (digestCode parts) []).1 ≠
      (eval H (SdkC_Oracle.program (digestCode parts))).2 := by
  have ideal : (eval H (SdkC_Oracle.program (digestCode parts))).2 = ok (encodeState (H (flatten parts))) := rfl
  refine ⟨ideal,?_⟩
  rw [digest_trace,returned,List.nil_append,ideal]
  intro equal
  have d := congrArg decodeState (Result.ok.inj equal)
  rw [state_roundtrip] at d
  exact different d.symm

#print axioms excluded
#print axioms different_execution
end AspisR1.ARU_IssuedMismatch
end
