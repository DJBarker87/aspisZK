import S9SourceResultTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9LoopSuccessTransportV1
open AspisR1S9SourceResultTransportV1

def mapFlow {A B C D : Type} (f : A → C) (g : B → D) : ControlFlow A B → ControlFlow C D
  | .cont a => .cont (f a)
  | .done b => .done (g b)

/-- Successful deterministic loops transport through the same per-step state
map. The measure proves termination only along successful continuations. No
independent target-loop-success premise is supplied. -/
theorem loop_success_transport {A B C D : Type}
    (step : A → Result (ControlFlow A B)) (target : C → Result (ControlFlow C D))
    (f : A → C) (g : B → D) (measure : A → Nat)
    (hstep : ∀ s, target (f s) = mapResult (mapFlow f g) (step s))
    (hdecrease : ∀ s s', step s = .ok (.cont s') → measure s' < measure s) :
    ∀ s out, Aeneas.Std.loop step s = .ok out → Aeneas.Std.loop target (f s) = .ok (g out) := by
  intro s out
  induction hm : measure s using Nat.strong_induction_on generalizing s out with
  | h n ih =>
    intro hrun
    rw [Aeneas.Std.loop.eq_def] at hrun
    cases hs : step s with
    | fail e => rw [hs] at hrun; cases hrun
    | div => rw [hs] at hrun; cases hrun
    | ok flow =>
      rw [hs] at hrun
      rw [Aeneas.Std.loop.eq_def,hstep,hs]
      cases flow with
      | done value =>
        change .ok value = .ok out at hrun
        have he : value = out := Result.ok.inj hrun
        subst out
        rfl
      | cont next =>
        change Aeneas.Std.loop step next = .ok out at hrun
        change Aeneas.Std.loop target (f next) = .ok (g out)
        have hlt := hdecrease s next hs
        have hn : measure next < n := by omega
        exact ih (measure next) hn next out rfl hrun

#print axioms loop_success_transport
end AspisR1S9LoopSuccessTransportV1
