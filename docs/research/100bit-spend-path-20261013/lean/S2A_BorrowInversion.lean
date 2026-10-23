import S2TrustedSdkBorrow

/-! Successful replies at fixed cuts of a single execution. `W` is the native
state carrier supplied by the SDK interpretation, not the consistency model.
No production `Library` instance, whole adapter simulation, or existence of
these cuts is asserted here. Each equation is the actual step at that cut. -/
set_option autoImplicit false
namespace AspisR1.S2A
open S2Trust

/-- Determinism identifies the post-state in the trust witness with the actual
post-state of this execution. No independent successful execution is selected. -/
theorem actual_step {W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (before after : W) (s : Heap F)
    (op : Op) (reply : Reply) (related : L.related before s)
    (valid : Valid s) (enabled : Enabled s op)
    (executed : L.run before op = (after, reply)) :
    reply = (run s op).2 ∧ L.related after (run s op).1 := by
  obtain ⟨w', step, post⟩ := trust.borrow_frame before s op related valid enabled
  rw [executed] at step
  have states : after = w' := congrArg Prod.fst step
  exact ⟨congrArg Prod.snd step, by simpa only [states] using post⟩

/-- An actual successful checkpoint acquisition forces the original cell free.
The typed interpretation and provenance stay in `L.related`; no integer
address equality is substituted for guard identity. -/
theorem exclusive_admission {W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (before after : W) (s : Heap F)
    (account token owner : Nat) (related : L.related before s)
    (valid : Valid s) (enabled : Enabled s (.exclusive account token owner))
    (executed : L.run before (.exclusive account token owner) = (after, .guard token)) :
    s.counter (s.accounts account).1 = 0 ∧
      L.related after (acquire s (s.accounts account).1 token owner .exclusive) := by
  obtain ⟨reply, post⟩ := actual_step L trust before after s
    (.exclusive account token owner) (.guard token) related valid enabled executed
  by_cases free : s.counter (s.accounts account).1 = 0
  · exact ⟨free, by simpa only [run, if_pos free] using post⟩
  · simp only [run, if_neg free] at reply
    cases reply

/-- An actual successful public/proof acquisition forces the shared-counter
bounds at THAT cut, rather than assuming them from a forward constructor. -/
theorem shared_admission {W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (before after : W) (s : Heap F)
    (account token owner : Nat) (related : L.related before s)
    (valid : Valid s) (enabled : Enabled s (.shared account token owner))
    (executed : L.run before (.shared account token owner) = (after, .guard token)) :
    (0 ≤ s.counter (s.accounts account).1 ∧
      s.counter (s.accounts account).1 < maxCounter) ∧
      L.related after (acquire s (s.accounts account).1 token owner .shared) := by
  obtain ⟨reply, post⟩ := actual_step L trust before after s
    (.shared account token owner) (.guard token) related valid enabled executed
  by_cases allowed : 0 ≤ s.counter (s.accounts account).1 ∧
      s.counter (s.accounts account).1 < maxCounter
  · exact ⟨allowed, by simpa only [run, if_pos allowed] using post⟩
  · simp only [run, if_neg allowed] at reply
    cases reply

/-- At a valid related state, dereferencing the actual shared guard returns the
entire modeled payload (descriptor, provenance and ALL contents coordinates).
This does not assert that the payload is still the original public input:
that causal frame is a separate enclosing-prefix obligation. -/
theorem shared_read {W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (before after : W) (s : Heap F)
    (token : Nat) (g : Guard) (payload : Payload)
    (related : L.related before s) (valid : Valid s)
    (guard : lookup s token = some g) (kind : g.kind = .shared)
    (executed : L.run before (.deref token) = (after, .payload payload)) :
    payload = s.payload g.cell ∧ L.related after s := by
  obtain ⟨w', step, post⟩ := trust.shared_deref before s token g related valid guard kind
  rw [executed] at step
  have states : after = w' := congrArg Prod.fst step
  have replies := congrArg Prod.snd step
  have bytes : payload = s.payload g.cell := Reply.payload.inj replies
  exact ⟨bytes, by simpa only [states] using post⟩

#print axioms actual_step
#print axioms exclusive_admission
#print axioms shared_admission
#print axioms shared_read
end AspisR1.S2A
