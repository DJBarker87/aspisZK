import Port6CK_Reader
import VTop_OracleCode
import CheckpointBytes5Inputs

/-! Translation of the existing extracted checkpoint effect code. A successful
native digest instruction emits exactly one observation; its exact returned
array selects the continuation. There is no parser/model input selection here.
The inherited per-digest Oracle interpretation identifies that observation.
Inner Err retains the prefix, including repeated reads; no suffix is appended. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port8EFF_CheckpointCode
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1DigestLogCarrier (flatten)

/-- Lift actual successful digest instructions, rather than synthesize a log
from their terminal return. Outer failures preserve already executed reads. -/
def program {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) : CheckpointBytes5Effect.Code A → Program Bytes State (Result A)
  | .done a => .done (.ok a)
  | .step r k => VTop_OracleCode.continueWith r (fun b => program D hash (k b))
  | .read parts k => VTop_OracleCode.continueWith (D.digest hash parts)
      (fun b => .ask (flatten parts) (fun _ => program D hash (k b)))

/-- All outcomes, without acceptance or an oracle law. -/
theorem value {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (code : CheckpointBytes5Effect.Code A) (H : Bytes → State) :
    (eval H (program D hash code)).2 = CheckpointBytes5Effect.erase D hash code := by
  induction code with
  | done a => rfl
  | step r k ih => cases r <;> simp only [program,VTop_OracleCode.continueWith,
      eval,CheckpointBytes5Effect.erase,bind_tc_ok,bind_tc_fail,bind_tc_div,ih]
  | read parts k ih => cases h : D.digest hash parts <;>
      simp only [program,h,VTop_OracleCode.continueWith,eval,
        CheckpointBytes5Effect.erase,bind_tc_ok,bind_tc_fail,bind_tc_div,ih]

/-- Complete ordered effects on every successful outer Result, including Rust
Err. The before log is arbitrary; duplicates are retained by append. -/
theorem effects {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (code : CheckpointBytes5Effect.Code A) (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle D hash H)
    (a : A) (before after : CheckpointBytes5Effect.Log)
    (ran : CheckpointBytes5Effect.run D hash code before = ok (a,after)) :
    CheckpointBytes5Inputs.observe after = CheckpointBytes5Inputs.observe before ++
      (eval H (program D hash code)).1 ∧
    (eval H (program D hash code)).2 = ok a := by
  induction code generalizing before after with
  | done b =>
    cases Result.ok.inj ran
    exact ⟨(List.append_nil _).symm,rfl⟩
  | step r k ih =>
    cases r with
    | fail e => cases ran
    | div => cases ran
    | ok b => exact ih b before after ran
  | read parts k ih =>
    cases call : D.digest hash parts with
    | fail e => simp only [CheckpointBytes5Effect.run,call,bind_tc_fail] at ran; cases ran
    | div => simp only [CheckpointBytes5Effect.run,call,bind_tc_div] at ran; cases ran
    | ok b =>
      simp only [CheckpointBytes5Effect.run,call,bind_tc_ok] at ran
      obtain ⟨logs,out⟩ := ih b _ after ran
      refine ⟨?_,?_⟩
      · simpa only [program,call,VTop_OracleCode.continueWith,eval,
          CheckpointBytes5Inputs.observe,List.map_append,List.map_cons,List.map_nil,
          oracle _ _ call,List.append_assoc,List.singleton_append] using logs
      · simpa only [program,call,VTop_OracleCode.continueWith,eval] using out

#print axioms value
#print axioms effects
end AspisR1.Port8EFF_CheckpointCode
end
