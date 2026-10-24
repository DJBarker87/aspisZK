import Port9OR_Reply

/-! A fixed response-driven interpretation. The native dictionary contributes
ONLY its existing success/fail/div policy, never the successful reply. Native
interpretation is pointwise in H and is outside the sampled Program. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_Code
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open CheckpointBytes5Effect
open AspisR1DigestLogCarrier (flatten)

/-- Retain the existing primitive error policy; replace only successful bytes.
This dictionary interprets a fixed source tree AT H. It is not sampled. -/
def native {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (H : Bytes → State) : AspisR1Stage2.aspis_core.digest.Digest32 Hash :=
  { D with digest := fun hash parts => match D.digest hash parts with
    | .ok _ => .ok (Port9OR_Reply.digest (H (flatten parts)))
    | .fail e => .fail e
    | .div => .div }

/-- The Program is chosen before H. Every successful read continuation consumes
its actual .ask reply; failed native calls issue no query, as before. -/
def program {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) : Code A → Program Bytes State (Result A)
  | .done a => .done (.ok a)
  | .step r k => VTop_OracleCode.continueWith r (fun b => program D hash (k b))
  | .read parts k => match D.digest hash parts with
    | .ok _ => .ask (flatten parts) (fun reply => program D hash (k (Port9OR_Reply.digest reply)))
    | .fail e => .done (.fail e)
    | .div => .done .div

/-- Total ordered native observation, including prefixes before OUTER failure.
The old StateT run loses such prefixes at its Result boundary. -/
def trace {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) : Code A → Log × Result A
  | .done a => ([],.ok a)
  | .step r k => match r with
    | .ok b => trace D hash (k b)
    | .fail e => ([],.fail e)
    | .div => ([],.div)
  | .read parts k => match D.digest hash parts with
    | .ok b => let rest := trace D hash (k b); ((parts,b)::rest.1,rest.2)
    | .fail e => ([],.fail e)
    | .div => ([],.div)

theorem trace_value {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (code : Code A) : (trace D hash code).2 = erase D hash code := by
  induction code with
  | done a => rfl
  | step r k ih => cases r <;> simp only [trace,erase,bind_tc_ok,bind_tc_fail,bind_tc_div,ih]
  | read parts k ih => cases call : D.digest hash parts <;>
      simp only [trace,erase,call,bind_tc_ok,bind_tc_fail,bind_tc_div,ih]

/-- Pointwise equality of COMPLETE source returns and ordered effects for every
H, with no acceptance/agreement premise. The fixed Program is on the left. -/
theorem correspondence {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (code : Code A) (H : Bytes → State) :
    eval H (program D hash code) =
      (CheckpointBytes5Inputs.observe (trace (native D H) hash code).1,
        (trace (native D H) hash code).2) := by
  induction code with
  | done a => rfl
  | step r k ih => cases r <;>
      simp only [program,VTop_OracleCode.continueWith,eval,trace,ih,CheckpointBytes5Inputs.observe,List.map_nil]
  | read parts k ih => cases call : D.digest hash parts <;>
      simp only [program,call,eval,trace,native,ih,CheckpointBytes5Inputs.observe,
        List.map_cons,List.map_nil,Port9OR_Reply.state_digest]

theorem value {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (code : Code A) (H : Bytes → State) :
    (eval H (program D hash code)).2 = erase (native D H) hash code := by
  rw [correspondence,trace_value]

/-- The historical per-successful-call Oracle fact is now proved for the
pointwise native interpretation, not required of one fixed D for all H. -/
theorem oracle {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) : CheckpointBytes5Inputs.Oracle (native D H) hash H := by
  intro parts d returned
  cases call : D.digest hash parts <;> simp only [native,call] at returned
  · cases Result.ok.inj returned
    exact Port9OR_Reply.state_digest _
  · cases returned
  · cases returned

#print axioms trace_value
#print axioms correspondence
#print axioms value
#print axioms oracle
end AspisR1.Port9OR_Code
end
