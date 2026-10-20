import Aeneas

/-!
A small operational model for `core::array::from_fn` in the extraction
harness. It calls a state-threading callback exactly once at each ascending
index, threads the returned closure state, and records outputs in call order.
The model retains `Result` failure/divergence behavior of the extracted
callback boundary. Its correspondence to Rust's library implementation is
premise P6 and is checked separately by the differential host test.
-/
open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FromFnP6

/-- A successful trace contains one callback transition per ascending index. -/
inductive StatefulFromFnTrace {S A : Type}
    (step : S → Nat → Result (A × S)) : Nat → Nat → S → List A → S → Prop
  | done (start : Nat) (state : S) :
      StatefulFromFnTrace step 0 start state [] state
  | call {count start : Nat} {state state' final : S} {value : A}
      {values : List A} :
      step state start = .ok (value, state') →
      StatefulFromFnTrace step count (start + 1) state' values final →
      StatefulFromFnTrace step (count + 1) start state (value :: values) final

/-- Run a callback in ascending index order, threading its returned state. -/
def statefulFromFnRun {S A : Type}
    (step : S → Nat → Result (A × S)) :
    Nat → Nat → S → Result (List A × S)
  | 0, _start, state => .ok ([], state)
  | count + 1, start, state => do
      let (value, state') ← step state start
      let (values, final) ← statefulFromFnRun step count (start + 1) state'
      .ok (value :: values, final)

theorem statefulFromFnRun_success_iff_trace {S A : Type}
    (step : S → Nat → Result (A × S)) :
    ∀ (count start : Nat) (state : S) (values : List A) (final : S),
      statefulFromFnRun step count start state = .ok (values, final) ↔
        StatefulFromFnTrace step count start state values final := by
  intro count
  induction count with
  | zero =>
      intro start state values final
      simp only [statefulFromFnRun]
      constructor
      · intro h
        cases Result.ok.inj h
        exact .done start state
      · intro h
        cases h
        rfl
  | succ count ih =>
      intro start state values final
      simp only [statefulFromFnRun]
      constructor
      · intro h
        cases hs : step state start with
        | fail e => simp [hs] at h
        | div => simp [hs] at h
        | ok pair =>
          rcases pair with ⟨value, state'⟩
          simp only [hs, bind_tc_ok] at h
          cases ht : statefulFromFnRun step count (start + 1) state' with
          | fail e => simp [ht] at h
          | div => simp [ht] at h
          | ok result =>
            rcases result with ⟨tail, final'⟩
            change (do
              let (tail', final'') ← statefulFromFnRun step count (start + 1) state'
              .ok (value :: tail', final'')) = .ok (values, final) at h
            rw [ht, bind_tc_ok] at h
            have hp := Result.ok.inj h
            rcases Prod.mk.inj hp with ⟨hvalues, hfinal⟩
            subst values
            subst final
            exact .call hs ((ih (start + 1) state' tail final').mp ht)
      · intro h
        cases h with
        | @call count start state state' final value values hstep htail =>
          have hrun := (ih (start + 1) state' values final).mpr htail
          simp [hstep, hrun]

/-- A local invariant is preserved along every successful callback transition. -/
theorem statefulFromFnTrace_preserves {S A : Type}
    {step : S → Nat → Result (A × S)}
    (stateOK : S → Nat → Prop) (valueOK : A → Prop)
    (hstep : ∀ state i value next,
      stateOK state i → step state i = .ok (value, next) →
      valueOK value ∧ stateOK next (i + 1)) :
    ∀ {count start state values final},
      stateOK state start →
      StatefulFromFnTrace step count start state values final →
      (∀ value, value ∈ values → valueOK value) ∧ stateOK final (start + count) := by
  intro count
  induction count with
  | zero =>
      intro start state values final hstate htrace
      cases htrace
      constructor
      · intro value hv
        cases hv
      · exact hstate
  | succ count ih =>
      intro start state values final hstate htrace
      cases htrace with
      | @call count start state state' final value values hcall htail =>
          obtain ⟨hvalue, hnext⟩ := hstep state start value state' hstate hcall
          obtain ⟨hall, hfinal⟩ := ih hnext htail
          constructor
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact hvalue
            · exact hall x hx
          · have hidx : start + 1 + count = start + (count + 1) := by omega
            rw [← hidx]
            exact hfinal

/-- Successful traces have exactly `count` outputs. -/
theorem statefulFromFnTrace_length {S A : Type}
    {step : S → Nat → Result (A × S)} :
    ∀ {count start state values final},
      StatefulFromFnTrace step count start state values final → values.length = count := by
  intro count
  induction count with
  | zero =>
      intro start state values final h
      cases h
      rfl
  | succ count ih =>
      intro start state values final h
      cases h with
      | call hstep htail =>
        simp [ih htail]

#print axioms statefulFromFnRun_success_iff_trace
#print axioms statefulFromFnTrace_preserves
#print axioms statefulFromFnTrace_length

end AspisR1FromFnP6
