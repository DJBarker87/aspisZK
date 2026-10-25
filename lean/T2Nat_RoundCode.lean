import T2Nat_Silent
import Port4D_Round
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_RoundCode
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open T2Nat_Silent
variable {W : Type}
def round (ops : FinishOps W) (poly : Slice U8) (alpha claim : E) (r : Usize) :
    Silent (core.result.Result E verifier.Error) := do
  let we ← call (ops.field poly 0#usize)
  let we1 ← call (ops.field poly 4#usize)
  let lhs ← call (ops.add we we1)
  let m ← call (ops.quarter)
  let rhs ← call (ops.mulM claim m)
  let i ← call (lift (Std.Usize.wrapping_mul 3#usize r))
  call (ops.trace 15#u16 i lhs)
  let i1 ← call (lift (Std.Usize.wrapping_mul 3#usize r))
  let i2 ← call (lift (Std.Usize.wrapping_add i1 1#usize))
  call (ops.trace 15#u16 i2 rhs)
  let b ← call (ops.ne lhs
      rhs)
  if b
  then pure (core.result.Result.Err verifier.Error.Relation)
  else
    let claim1 ← call (ops.polynomial poly alpha)
    let i3 ← call (lift (Std.Usize.wrapping_mul 3#usize r))
    let i4 ← call (lift (Std.Usize.wrapping_add i3 2#usize))
    call (ops.trace 15#u16 i4 claim1)
    pure (core.result.Result.Ok claim1)

theorem round_erase (ops : FinishOps W) (poly : Slice U8) (alpha claim : E) (r : Usize) :
    erase (round ops poly alpha claim r) = Port4D_Round.round ops poly alpha claim r := by
  simp only [round,Port4D_Round.round,erase_bind,erase_call,erase_pure]
  repeat
    first
    | rfl
    | (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro x hx)
    | (split <;> simp only [erase_bind,erase_call,erase_pure])

theorem round_effects {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (ops : FinishOps W) (poly : Slice U8) (alpha claim : E) (r : Usize)
    (before : CheckpointBytes5Effect.Log) :
    CheckpointBytes5Effect.run D hash (code (round ops poly alpha claim r)) before =
      (do let result ← Port4D_Round.round ops poly alpha claim r; ok (result,before)) := by
  rw [ordered_log,round_erase]

#print axioms round_erase
#print axioms round_effects
end AspisR1.T2Nat_RoundCode
end
