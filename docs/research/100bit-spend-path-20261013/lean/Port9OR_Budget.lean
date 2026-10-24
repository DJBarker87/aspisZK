import Port9OR_Bodies
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_Budget
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Structural upper bound, including branches ending in outer failure. -/
def bounded {A : Type} : Nat → CheckpointBytes5Effect.Code A → Prop
  | _, .done _ => True
  | n, .step _ k => ∀ b, bounded n (k b)
  | n, .read _ k => 0<n ∧ ∀ b, bounded (n-1) (k b)

theorem count {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (code : CheckpointBytes5Effect.Code A) (H : Bytes → State)
    (n : Nat) (bound : bounded n code) :
    (eval H (Port9OR_Code.program D hash code)).1.length≤n := by
  induction code generalizing n with
  | done a => exact Nat.zero_le n
  | step r k ih =>
    cases r with
    | fail e => exact Nat.zero_le n
    | div => exact Nat.zero_le n
    | ok b => exact ih b n (bound b)
  | read parts k ih =>
    cases call : D.digest hash parts with
    | fail e => simpa only [Port9OR_Code.program,call,eval,List.length_nil] using Nat.zero_le n
    | div => simpa only [Port9OR_Code.program,call,eval,List.length_nil] using Nat.zero_le n
    | ok b =>
      have positive : 0<n := bound.1
      have rest := ih (Port9OR_Reply.digest (H (AspisR1DigestLogCarrier.flatten parts))) (n-1)
        (bound.2 _)
      simp only [Port9OR_Code.program,call,eval,List.length_cons]
      omega

/-- Syntactic budget of the emitted current parent: every early exit and
all helper failures remain in scope. The decoder tail has no digest calls. -/
theorem reader_bounded (ops : AspisR1Stage2.ResumeOps) (ck proof pub : Slice U8)
    (v : AspisR1Stage2.transport.Variant) :
    bounded 3 (Port8EFF_NativeReader.program ops ck proof pub v) := by
  unfold Port8EFF_NativeReader.program
  repeat' first
  | (solve | trivial)
  | (fail_if_no_progress simp only [CheckpointBytes5Effect.bind,CheckpointBytes5Effect.liftResult,
      CheckpointBytes5Effect.read,bounded])
  | intro x
  | constructor
  | split
  all_goals omega

/-- An all-input CHECKPOINT piece, not a whole-driver 1161 cap. -/
theorem reader_count (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (ck proof pub : Slice U8)
    (v : VTop_Stages.transport.Variant) (hash : Hash) (H : Bytes → State) :
    (eval H (Port9OR_Bodies.reader reserved unwrap D ck proof pub v hash)).1.length≤3 := by
  apply count
  unfold Port8EFF_Bodies.readerCode
  repeat' first
  | (solve | trivial)
  | (fail_if_no_progress simp only [CheckpointBytes5Effect.bind,CheckpointBytes5Effect.liftResult,
      CheckpointBytes5Effect.read,bounded,Port8EFF_NativeReader.program])
  | intro x
  | constructor
  | split
  all_goals omega

#print axioms count
#print axioms reader_bounded
#print axioms reader_count
end AspisR1.Port9OR_Budget
end
