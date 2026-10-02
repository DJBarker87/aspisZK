import Aeneas.Std

/-! A finite loop simulation helper. Its step equality and decreasing-rank
premises must be proved for a concrete source loop before it can be applied. -/
set_option autoImplicit false
namespace AspisV8R19.R199FiniteLoopMap
open Aeneas Aeneas.Std Result ControlFlow

def mapControl {S T B : Type} (stateMap : S → T) :
    ControlFlow S B → ControlFlow T B
  | .cont s => .cont (stateMap s)
  | .done b => .done b

theorem loop_map {S T B : Type}
    (f : S → Result (ControlFlow S B))
    (g : T → Result (ControlFlow T B))
    (stateMap : S → T) (rank : S → Nat)
    (hstep : ∀ s, (do let cf ← f s; ok (mapControl stateMap cf)) = g (stateMap s))
    (hdecr : ∀ s next, f s = .ok (.cont next) → rank next < rank s)
    (s : S) : loop f s = loop g (stateMap s) := by
  have hloop : ∀ n s, rank s = n → loop f s = loop g (stateMap s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro s hn
        rw [loop.eq_def, loop.eq_def, ← hstep s]
        cases hf : f s with
        | fail e => simp [hf]
        | div => simp [hf]
        | ok cf =>
            cases cf with
            | done b => simp [hf, mapControl]
            | cont next =>
                have hlt : rank next < n := by simpa [hn] using hdecr s next hf
                simpa [hf, mapControl] using ih (rank next) hlt next rfl
  exact hloop (rank s) s rfl

#print axioms loop_map
end AspisV8R19.R199FiniteLoopMap
