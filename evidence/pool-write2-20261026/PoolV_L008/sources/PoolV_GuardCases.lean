import PoolW_ZeroGuard
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolV_GuardCases
open Aeneas Aeneas.Std Result
open PoolW_ZeroGuard

theorem accepted_metadata (a : Account) (id : Key) (exact : Nat)
    (read : Result (core.result.Result (Slice U8) Error)) (exempt : Bool)
    (accepted : run a id exact read exempt = ok (.Ok ())) :
    a.owner = id ∧ a.executable = false ∧ a.is_writable = true := by
  have admission : Hiq_PoolSource.history.require_program_account a id true = ok (.Ok ()) := by
    cases h : Hiq_PoolSource.history.require_program_account a id true with
    | fail e => simp [run,h] at accepted
    | div => simp [run,h] at accepted
    | ok r =>
      cases r with
      | Err e => simp [run,h] at accepted
      | Ok u => cases u; exact h
  exact (Hiq_PoolGuards.account_iff a id true).mp admission

theorem accepted_iff (a : Account) (id : Key) (exact : Nat) (data : Slice U8) (exempt : Bool) :
    run a id exact (ok (.Ok data)) exempt = ok (.Ok ()) ↔
      (a.owner = id ∧ a.executable = false ∧ a.is_writable = true) ∧
      data.val.length = exact ∧ (∀ byte ∈ data.val, byte = 0#u8) ∧ exempt = true := by
  constructor
  · intro h
    have meta := accepted_metadata a id exact _ exempt h
    have admission := (Hiq_PoolGuards.account_iff a id true).mpr meta
    exact ⟨meta,(PoolW_ZeroGuard.accepted a id exact data exempt admission).mp h⟩
  · rintro ⟨meta,rest⟩
    have admission := (Hiq_PoolGuards.account_iff a id true).mpr meta
    exact (PoolW_ZeroGuard.accepted a id exact data exempt admission).mpr rest

theorem no_occupied_success (a : Account) (id : Key) (exact : Nat) (data : Slice U8) (exempt : Bool)
    (occupied : ∃ byte ∈ data.val, byte ≠ 0#u8) :
    run a id exact (ok (.Ok data)) exempt ≠ ok (.Ok ()) := by
  intro success
  have allzero := ((accepted_iff a id exact data exempt).mp success).2.2.1
  rcases occupied with ⟨byte,member,nonzero⟩
  exact nonzero (allzero byte member)

theorem rejects_read_error (a : Account) (id : Key) (exact : Nat) (exempt : Bool) (e : Error) :
    run a id exact (ok (.Err e)) exempt ≠ ok (.Ok ()) := by
  intro accepted
  have admission := (Hiq_PoolGuards.account_iff a id true).mpr
    (accepted_metadata a id exact _ exempt accepted)
  simp [run,admission] at accepted

#print axioms accepted_metadata
#print axioms accepted_iff
#print axioms no_occupied_success
#print axioms rejects_read_error
end AspisR1.PoolV_GuardCases
end
