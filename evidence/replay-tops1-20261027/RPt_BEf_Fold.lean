import RPt_BEf_Carrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_Fold
open Aeneas Aeneas.Std Result SdkC_Source

/-- Replay only the carrier transitions of the recorded attempted calls.
The failed final call is included. Existing prefix entries are not replayed. -/
def replay {S : Type} (call : Parts → S → Result Digest × S) : Log → S → S
  | [], state => state
  | q::rest, state => replay call rest (call q.parts state).2

theorem append {S : Type} (call : Parts → S → Result Digest × S)
    (left right : Log) (state : S) :
    replay call (left ++ right) state = replay call right (replay call left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons q rest ih => exact ih _

/-- Exact state reconstruction, without a frame or success assumption. -/
theorem carrier {S A : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (state : S) (before : Log) :
    ∃ suffix,
      (BEf_Carrier.run call code state before).2.2 = before ++ suffix ∧
      (BEf_Carrier.run call code state before).2.1 = replay call suffix state := by
  induction code generalizing state before with
  | done a => exact ⟨[], (List.append_nil _).symm, rfl⟩
  | step r k ih =>
    cases r with
    | ok a => exact ih a state before
    | fail e => exact ⟨[], (List.append_nil _).symm, rfl⟩
    | div => exact ⟨[], (List.append_nil _).symm, rfl⟩
  | read parts k ih =>
    unfold BEf_Carrier.run
    split
    next answer next h =>
      have transition : (call parts state).2 = next := by rw [h]
      cases answer with
      | ok digest =>
        obtain ⟨suffix,logEq,stateEq⟩ := ih digest next (before ++ [⟨parts,.ok digest⟩])
        refine ⟨⟨parts,.ok digest⟩ :: suffix, ?_, ?_⟩
        · simpa only [List.append_assoc,List.singleton_append] using logEq
        · simpa only [replay,transition] using stateEq
      | fail e => exact ⟨[⟨parts,.fail e⟩], rfl, by simp only [replay,transition]⟩
      | div => exact ⟨[⟨parts,.div⟩], rfl, by simp only [replay,transition]⟩

#print axioms append
#print axioms carrier
end AspisR1.BEf_Fold
end
