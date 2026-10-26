import P6C_FullBoundary
set_option autoImplicit false
noncomputable section
namespace AspisR1.P6C_NativeEffects
open Aeneas Aeneas.Std Result SdkC_Source

def values (log : Log) : CheckpointBytes5Effect.Log := log.filterMap fun q =>
  match q.returned with
  | .ok value => some (q.parts,value)
  | _ => none

def forget {A : Type} (answer : Result A × Log) : Result (A × CheckpointBytes5Effect.Log) :=
  match answer.1 with
  | .ok value => .ok (value,values answer.2)
  | .fail e => .fail e
  | .div => .div

theorem values_append (left right : Log) :
    values (left ++ right) = values left ++ values right := List.filterMap_append

/-- The existing native effect interpreter is exactly the successful-log
projection of the partial interpreter. Failed prefixes remain available in
Source.run; this projection's failure output does not purport to retain them. -/
theorem source {Hash A : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (hashv : Parts → Result Digest) (binding : ∀ parts, D.digest hash parts = hashv parts)
    (code : Code A) (before : Log) :
    CheckpointBytes5Effect.run D hash code (values before) = forget (run hashv code before) := by
  induction code generalizing before with
  | done a => rfl
  | step r k ih =>
    cases r with
    | fail e => rfl
    | div => rfl
    | ok a => exact ih a before
  | read parts k ih =>
    simp only [CheckpointBytes5Effect.run,binding]
    cases actual : hashv parts with
    | fail e => simp only [run,actual,bind_tc_fail,forget]
    | div => simp only [run,actual,bind_tc_div,forget]
    | ok digest =>
      simp only [run,actual,bind_tc_ok]
      have next : values (before ++ [⟨parts,ok digest⟩]) = values before ++ [(parts,digest)] := by
        rw [values_append]
        rfl
      rw [← next]
      exact ih digest _

/-- Complete successful native value AND ordered effects, under the actual
partial digest dictionary. All calls, including duplicates, remain in place. -/
theorem accepted {Hash A : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (hashv : Parts → Result Digest) (binding : ∀ parts, D.digest hash parts = hashv parts)
    (code : Code A) (value : A)
    (success : (run hashv code []).1 = ok value) :
    CheckpointBytes5Effect.run D hash code [] =
      ok (value,values (run hashv code []).2) := by
  have same := source D hash hashv binding code []
  simpa only [values,List.filterMap_nil,forget,success] using same

/-- On accepted source executions the projection loses NO issued attempts. -/
theorem no_lost_calls {A : Type} (hashv : Parts → Result Digest)
    (code : Code A) (value : A) (accepted : (run hashv code []).1 = ok value) :
    (values (run hashv code []).2).length = (run hashv code []).2.length := by
  have successes := P6C_Accepted.issued_calls_ok hashv code [] value accepted (by simp)
  generalize h : (run hashv code []).2 = log at successes ⊢
  clear h
  induction log with
  | nil => rfl
  | cons q rest ih =>
    obtain ⟨digest,returned⟩ := successes q (List.mem_cons_self ..)
    simp only [values,List.filterMap_cons,returned,List.length_cons]
    have tail := ih (fun q member => successes q (List.mem_cons_of_mem _ member))
    exact congrArg Nat.succ tail

#print axioms values_append
#print axioms source
#print axioms accepted
#print axioms no_lost_calls
end AspisR1.P6C_NativeEffects
end
