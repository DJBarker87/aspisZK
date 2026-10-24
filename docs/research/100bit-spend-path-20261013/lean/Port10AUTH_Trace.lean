import Port9OR_Code

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_Trace
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open Port9OR_Code

/-- Concatenation retains the entire executed prefix even if the continuation
fails. There is no acceptance or totality premise. -/
theorem trace_bind {A B Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (p : Code A) (k : A → Code B) :
    trace D hash (p >>= k) =
      match trace D hash p with
      | (before, .ok a) => let after := trace D hash (k a); (before ++ after.1, after.2)
      | (before, .fail e) => (before, .fail e)
      | (before, .div) => (before, .div) := by
  change trace D hash (CheckpointBytes5Effect.bind p k) = _
  induction p with
  | done a => simp only [CheckpointBytes5Effect.bind,trace,List.nil_append]
  | step r c ih => cases r <;> simp only [CheckpointBytes5Effect.bind,trace,ih]
  | read parts c ih =>
    cases call : D.digest hash parts <;> simp only [CheckpointBytes5Effect.bind,trace,call,ih]
    cases h : trace D hash (c _) with
    | mk before result => cases result <;> simp only [List.cons_append]

/-- On actual success, the historical StateT run and total-prefix observation
agree exactly, for any initial log. -/
theorem run_of_trace {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (p : Code A) (a : A) (before : Log)
    (success : (trace D hash p).2=ok a) :
    run D hash p before=ok (a,before++(trace D hash p).1) := by
  induction p generalizing before with
  | done b => cases Result.ok.inj success; simp only [run,trace,List.append_nil]
  | step r k ih => cases r with
    | fail e => cases success
    | div => cases success
    | ok b => exact ih b before success
  | read parts k ih =>
    cases call : D.digest hash parts with
    | fail e => simp only [trace,call] at success;cases success
    | div => simp only [trace,call] at success;cases success
    | ok b =>
      simp only [trace,call] at success
      simpa only [run,trace,call,bind_tc_ok,List.append_assoc,List.singleton_append] using
        ih b (before++[(parts,b)]) success

theorem trace_lift {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (r : Result A) : trace D hash (liftResult r) = ([],r) := by
  cases r <;> rfl

#print axioms trace_lift
#print axioms trace_bind
#print axioms run_of_trace
end AspisR1.Port10AUTH_Trace
end
