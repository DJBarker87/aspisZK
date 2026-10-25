import SdkC_Source
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkC_Source
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Relate actual typed source digest dictionaries to partial instrumentation.
The equation is pointwise source association, never an oracle-totality claim. -/
theorem erasure_to {Hash A : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (hashv : Parts → Result Digest) (source : ∀ parts, D.digest hash parts = hashv parts)
    (code : Code A) (before : Log) :
    (run hashv code before).1 = CheckpointBytes5Effect.erase D hash code := by
  induction code generalizing before with
  | done a => rfl
  | step r k ih =>
    cases r <;> simp only [run,CheckpointBytes5Effect.erase,bind_tc_ok,bind_tc_fail,bind_tc_div]
    all_goals first | rfl | apply ih
  | read parts k ih =>
    simp only [CheckpointBytes5Effect.erase,source]
    cases h : hashv parts <;> simp only [run,h,bind_tc_ok,bind_tc_fail,bind_tc_div]
    all_goals first | rfl | apply ih

/-- Prefixes are retained across monadic failure, not just successful calls. -/
def resume {A B : Type} (hashv : Parts → Result Digest)
    (first : Result A × Log) (next : A → Code B) : Result B × Log :=
  match first.1 with
  | .ok a => run hashv (next a) first.2
  | .fail e => (.fail e,first.2)
  | .div => (.div,first.2)

theorem run_bind (hashv : Parts → Result Digest) {A B : Type}
    (code : Code A) (next : A → Code B) (before : Log) :
    run hashv (code >>= next) before = resume hashv (run hashv code before) next := by
  induction code generalizing before with
  | done a => rfl
  | step r k ih =>
    cases r with
    | ok a => exact ih a before
    | fail e => rfl
    | div => rfl
  | read parts k ih =>
    change run hashv (.read parts (fun d => CheckpointBytes5Effect.bind (k d) next)) before = _
    cases h : hashv parts with
    | ok d => simpa only [run,h] using ih d (before ++ [⟨parts,.ok d⟩])
    | fail e => simp only [run,h,resume]
    | div => simp only [run,h,resume]

theorem read_count (log : Log) : (readLog log).length ≤ log.length := by
  exact List.length_filterMap_le _ _

/-- Every successful native hash reply is bound to the existing ROM world;
no fabricated reply can occur in a reified source execution. -/
theorem no_fabricated_reply (hashv : Parts → Result Digest) (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    {A : Type} (code : Code A) (a : Bytes) (d : State) (bad : d ≠ H a) :
    (a,d) ∉ readLog (run hashv code []).2 := by
  intro member
  exact bad (consistent hashv sha256 H p1 syscall code (a,d) member)

/-- Non-vacuity is a literal returning source execution, not an assumed log. -/
theorem returning_digest (hashv : Parts → Result Digest) (parts : Parts) (digest : Digest)
    (success : hashv parts = .ok digest) :
    run hashv (digestCode parts) [] = (.ok digest,[⟨parts,.ok digest⟩]) := by
  rw [digest_trace,success,List.nil_append]

/-- Rejection still charges the attempted syscall. -/
theorem failed_digest (hashv : Parts → Result Digest) (parts : Parts) (error : Error)
    (failure : hashv parts = .fail error) :
    run hashv (digestCode parts) [] = (.fail error,[⟨parts,.fail error⟩]) := by
  rw [digest_trace,failure,List.nil_append]

#print axioms erasure_to
#print axioms run_bind
#print axioms read_count
#print axioms no_fabricated_reply
#print axioms returning_digest
#print axioms failed_digest
end AspisR1.SdkC_Source
end
