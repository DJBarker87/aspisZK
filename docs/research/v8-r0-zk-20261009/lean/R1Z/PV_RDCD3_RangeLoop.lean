import R1Z.PV_RDCD3_RangeFold

namespace R1Z.PV_RDCD3_RangeLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow PV_RDCD3_RangeFold

/-- The source loop state owns both the iterator and the accumulator. -/
def body {S : Type} (f : S → Nat → Result S) (state : Cursor × S) :
    Result (ControlFlow (Cursor × S) S) :=
  match next state.1 with
  | (none,_) => ok (done state.2)
  | (some x,r') => do let acc' ← f state.2 x; ok (cont (r',acc'))

/-- Source-shaped while-let fold, without fuel or a default successful cutoff. -/
def source {S : Type} (f : S → Nat → Result S) (r : Cursor) (acc : S) : Result S :=
  loop (body f) (r,acc)

theorem complete {S : Type} (f : S → Nat → Result S) (fuel start stop : Nat)
    (acc : S) (bound : stop=start+fuel) :
    source f ⟨start,stop⟩ acc = ordered f fuel start acc := by
  induction fuel generalizing start acc with
  | zero =>
    simp only [Nat.add_zero] at bound
    subst stop
    rw [source,loop.eq_def]
    simp [body,next,ordered]
  | succ fuel ih =>
    have active : start < stop := by omega
    rw [source,loop.eq_def]
    simp only [body,next_active (⟨start,stop⟩ : Cursor) active,ordered]
    cases hf : f acc start with
    | ok out =>
      simp only [hf,bind_tc_ok]
      exact ih (start+1) out (by omega)
    | fail e => simp [hf]
    | div => simp [hf]

theorem empty {S : Type} (f : S → Nat → Result S) (r : Cursor) (acc : S)
    (empty : r.stop ≤ r.start) : source f r acc = ok acc := by
  rw [source,loop.eq_def]
  simp [body,next_empty r empty]

/-- Arbitrary endpoints, including reversed/empty ranges. -/
theorem all_endpoints {S : Type} (f : S → Nat → Result S) (r : Cursor) (acc : S) :
    source f r acc = ordered f (r.stop-r.start) r.start acc := by
  by_cases h : r.start ≤ r.stop
  · exact complete f (r.stop-r.start) r.start r.stop acc (by omega)
  · rw [empty f r acc (by omega)]
    simp only [show r.stop-r.start=0 from by omega,ordered]

#print axioms complete
#print axioms empty
#print axioms all_endpoints
end R1Z.PV_RDCD3_RangeLoop
