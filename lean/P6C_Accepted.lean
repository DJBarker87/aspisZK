import SdkC_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.P6C_Accepted
open Aeneas Aeneas.Std Result SdkC_Source

/-- No failing or diverging read can occur in the suffix of a returning source
execution. The prefix is explicit because it may belong to an earlier run. -/
theorem issued_calls_ok (hashv : Parts → Result Digest) {A : Type}
    (code : Code A) (before : Log) (value : A)
    (accepted : (run hashv code before).1 = ok value)
    (initial : ∀ q ∈ before, ∃ digest, q.returned = ok digest) :
    ∀ q ∈ (run hashv code before).2,
      ∃ digest, q.returned = ok digest := by
  induction code generalizing before with
  | done a => exact initial
  | step r k ih =>
    cases r with
    | fail e => cases accepted
    | div => cases accepted
    | ok a => exact ih a before accepted initial
  | read parts k ih =>
    cases actual : hashv parts with
    | fail e => simp only [run,actual] at accepted; cases accepted
    | div => simp only [run,actual] at accepted; cases accepted
    | ok digest =>
      simp only [run,actual] at accepted ⊢
      apply ih digest _ accepted
      intro q member
      rcases List.mem_append.mp member with old | fresh
      · exact initial q old
      · obtain rfl := List.mem_singleton.mp fresh
        exact ⟨digest,rfl⟩

/-- The source log identifies actual syscall success, not merely a success
label in a freely supplied trace. -/
theorem actual_calls_ok (hashv : Parts → Result Digest) {A : Type}
    (code : Code A) (value : A)
    (accepted : (run hashv code []).1 = ok value) :
    ∀ q ∈ (run hashv code []).2, ∃ digest,
      q.returned = ok digest ∧ hashv q.parts = ok digest := by
  intro q member
  obtain ⟨digest,returned⟩ := issued_calls_ok hashv code [] value accepted (by simp) q member
  exact ⟨digest,returned,(associated hashv code [] (by simp) q member).symm.trans returned⟩

/-- Any replacement agreeing on successful syscall returns preserves the
complete accepted Result and ordered attempt log. No value at a non-issued
input is used, and duplicate reads remain duplicate reads. -/
theorem extension_irrelevant (hashv replacement : Parts → Result Digest)
    (agrees : ∀ parts digest, hashv parts = ok digest → replacement parts = ok digest)
    {A : Type} (code : Code A) (before : Log) (value : A)
    (accepted : (run hashv code before).1 = ok value) :
    run replacement code before = run hashv code before := by
  induction code generalizing before with
  | done a => rfl
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
      simp only [run,actual,agrees parts digest actual] at accepted ⊢
      exact ih digest _ accepted

#print axioms issued_calls_ok
#print axioms actual_calls_ok
#print axioms extension_irrelevant
end AspisR1.P6C_Accepted
end
