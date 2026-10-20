import Stage2ContinuationLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace Stage2ContinuationOwnedLoop
variable {A B E : Type}
abbrev State (A B E : Type) := core.result.Result (A × B) E
abbrev Call (A B E : Type) := A → B → Result (State A B E)

def body (next : A → Nat) (call : Call A B E) : State A B E →
    Result (ControlFlow (State A B E) (State A B E))
  | .Err e => ok (done (.Err e))
  | .Ok (a,b) => do
    if 22 ≤ next a then ok (done (.Ok (a,b)))
    else
      let r ← call a b
      ok (cont r)

def run (next : A → Nat) (call : Call A B E) (a : A) (b : B) :=
  Aeneas.Std.loop (body next call) (.Ok (a,b))

def adapt (call : Call A B E) : Stage2ContinuationLoop.Call A B E := fun a b => do
  let r ← call a b
  match r with
  | .Ok (a1,b1) => ok (.Ok (),a1,b1)
  | .Err e => ok (.Err e,a,b)

private theorem loop_error (next : A → Nat) (call : Call A B E) (e : E) :
    Aeneas.Std.loop (body next call) (.Err e) = ok (.Err e) := by
  rw [Aeneas.Std.loop.eq_def]
  rfl

theorem successful_loop_chain (next : A → Nat) (call : Call A B E)
    (advance : ∀ a a1 b b1, call a b = ok (.Ok (a1,b1)) → next a1 = next a + 1)
    (a out : A) (b bout : B) (ha : next a ≤ 22)
    (h : run next call a b = ok (.Ok (out,bout))) :
    Stage2ContinuationLoop.Chain next (adapt call) a b out bout (22-next a) := by
  change Aeneas.Std.loop (body next call) (.Ok (a,b)) = ok (.Ok (out,bout)) at h
  induction hfuel : 22-next a generalizing a b with
  | zero =>
    have he : next a = 22 := by omega
    rw [Aeneas.Std.loop.eq_def] at h
    have hp : a = out ∧ b = bout := by simpa [body,he] using h
    rcases hp with ⟨rfl,rfl⟩
    exact Stage2ContinuationLoop.Chain.done a b he
  | succ k ih =>
    have active : next a < 22 := by omega
    have inactive : ¬22 ≤ next a := by omega
    rw [Aeneas.Std.loop.eq_def] at h
    simp only [body,if_neg inactive] at h
    cases hc : call a b with
    | fail e => simp [hc] at h
    | div => simp [hc] at h
    | ok state =>
      have ht : Aeneas.Std.loop (body next call) state = ok (.Ok (out,bout)) := by
        simpa [hc] using h
      cases state with
      | Err e => rw [loop_error] at ht; cases ht
      | Ok pair =>
        rcases pair with ⟨a1,b1⟩
        have hnext := advance a a1 b b1 hc
        have hchain : Stage2ContinuationLoop.Chain next (adapt call) a1 b1 out bout k := by
          apply ih (a := a1) (b := b1)
          · omega
          · exact ht
          · omega
        apply Stage2ContinuationLoop.Chain.step active ?_ hchain
        simp [adapt,hc]

theorem twelve_ordered_calls (next : A → Nat) (call : Call A B E)
    (advance : ∀ a a1 b b1, call a b = ok (.Ok (a1,b1)) → next a1 = next a + 1)
    (a out : A) (b bout : B) (start : next a = 10)
    (h : run next call a b = ok (.Ok (out,bout))) :
    Stage2ContinuationLoop.Chain next (adapt call) a b out bout 12 := by
  have hc := successful_loop_chain next call advance a out b bout (by omega) h
  simpa only [start] using hc

#print axioms loop_error
#print axioms successful_loop_chain
#print axioms twelve_ordered_calls
end Stage2ContinuationOwnedLoop
