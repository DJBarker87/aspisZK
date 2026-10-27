import XRn_Join_ABI
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XRp_LoopReplay

/-- A finite certificate for the actual loop body, preserving every Result. -/
inductive Run {S T : Type} (body : S → Result (ControlFlow S T)) : S → Result T → Prop
  | done (s : S) (v : T) (h : body s = ok (.done v)) : Run body s (ok v)
  | fail (s : S) (e : Error) (h : body s = fail e) : Run body s (fail e)
  | div (s : S) (h : body s = div) : Run body s div
  | step (s next : S) (r : Result T) (h : body s = ok (.cont next))
      (tail : Run body next r) : Run body s r

theorem sound {S T : Type} (body : S → Result (ControlFlow S T))
    (s : S) (r : Result T) (run : Run body s r) : loop body s = r := by
  induction run with
  | done s v h => rw [loop.eq_def, h]
  | fail s e h => rw [loop.eq_def, h]
  | div s h => rw [loop.eq_def, h]
  | step s next r h tail ih => rw [loop.eq_def, h]; exact ih

#print axioms sound
end XRp_LoopReplay
