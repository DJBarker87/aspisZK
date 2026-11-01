import NEE_ValidatorOracle
set_option autoImplicit false
noncomputable section
namespace NEE_ValidatorMutation
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBN_StatementResult
abbrev LateError := pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
abbrev LateReply := Result (core.result.Result Unit LateError × Slice U8)

def mutate (f : Slice U8 → Slice U8) : LateReply → LateReply
  | .fail e => .fail e
  | .div => .div
  | .ok (status,out) => .ok (status,f out)

def ignore (r : LateReply) : NED_ValidatorTrace.R := do
  let (status,_) ← r
  match status with
  | .Err e => ok (.Err (.LaneTransition e))
  | .Ok _ => ok (.Ok ())

/-- The local buffer never escapes the validator, even on a child error. -/
theorem discard (r : LateReply) (f : Slice U8 → Slice U8) :
    ignore (mutate f r) = ignore r := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok p => rcases p with ⟨status,out⟩; cases status <;> rfl

abbrev Pay := Statement → Result (core.result.Result (Array U8 216#usize) PaymentError)
abbrev Lane := Array U32 8#usize → Result (core.result.Result U8 pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
abbrev Late := NBN_LateSummary.Statement → Slice U8 → LateReply

theorem tail (pay : Pay) (lane : Lane) (late : Late) (f : Slice U8 → Slice U8)
    (s : Statement) :
    NEE_ValidatorOracle.tail pay lane (fun a b => mutate f (late a b)) s =
    NEE_ValidatorOracle.tail pay lane late s := by
  unfold NEE_ValidatorOracle.tail
  dsimp only
  cases h : lane (parts s).2.2.2.2.1 with
  | fail e => simp only [h]
  | div => simp only [h]
  | ok p => cases p with
    | Err e => simp only [h]
    | Ok l =>
      simp only [h]
      split
      · rfl
      · change (ignore (mutate f (late _ _)),_) = (ignore (late _ _),_)
        rw [discard]

theorem bindings (pay : Pay) (lane : Lane) (late : Late) (f : Slice U8 → Slice U8)
    (s : Statement) :
    NEE_ValidatorOracle.bindings pay lane (fun a b => mutate f (late a b)) s =
    NEE_ValidatorOracle.bindings pay lane late s := by
  unfold NEE_ValidatorOracle.bindings
  repeat' first | split | rfl | exact tail pay lane late f s

/-- Arbitrary whole-buffer reply mutations preserve Result AND ordered calls. -/
theorem result_and_effects (pay : Pay) (lane : Lane) (late : Late)
    (f : Slice U8 → Slice U8) (s : Statement) :
    NEE_ValidatorOracle.run pay lane (fun a b => mutate f (late a b)) s =
    NEE_ValidatorOracle.run pay lane late s := by
  unfold NEE_ValidatorOracle.run
  split
  · rfl
  · split
    · rfl
    · cases pay s with
      | fail e => rfl
      | div => rfl
      | ok p => cases p with
        | Err e => rfl
        | Ok bytes => rw [bindings]

#print axioms discard
#print axioms tail
#print axioms bindings
#print axioms result_and_effects
end NEE_ValidatorMutation
