import PV_EVH_NativeStackDrop
import PV_EVH_Entropy
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyError
open Aeneas Aeneas.Std ProverRwFull ControlFlow
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_HeapOwnership (Key)
open PV_EVH_StackZero (Slot State Cleared)
open PV_EVH_StackCleanup (Q Run sameKey drop64)
abbrev Answer := ControlFlow Usize (core.result.Result
  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
  aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError)
abbrev Fill := Q ((core.result.Result Unit getrandom.error.Error) × Slice U8)

def returnedError (e : getrandom.error.Error) : Answer :=
  done (.Err (.Os e))

/-- The branch is the existing extraction, not a reference client. This is a
small symbolic error branch; it never reduces the entropy/retry recurrence. -/
theorem source_error [ExternalTypes] [ExternalFuns]
    (mask : Array U8 32#usize) (retry : Usize)
    (back : Slice U8 → zeroize.Zeroizing (Array U8 64#usize))
    (e : getrandom.error.Error) (s : Slice U8) :
    PV_EVH_Entropy.afterDraw mask retry back (.Err e) s = .ok (returnedError e) := rfl

/-- The ordinary error path uses the fill's complete post-world and the
original live stack key. Driver/entry admission is still not inferred here. -/
def afterFill (key : Key) (fill : Fill) (success : Slice U8 → Q Answer) : Q Answer := do
  let (r,s) ← fill
  match r with
  | .Ok _ => success s
  | .Err e => do
    let _ ← drop64 key
    pure (returnedError e)

theorem error_world (key : Key) (fill : Fill) (success : Slice U8 → Q Answer)
    (w : State) (e : getrandom.error.Error) (s : Slice U8) (slot : Slot)
    (hf : (fill w).outcome = .returned (.ok (.Err e,s)))
    (hs : (fill w).state.frame.live.find? (sameKey key) = some slot)
    (hn : slot.initialized = 64) :
    afterFill key fill success w =
      ⟨.returned (.ok (returnedError e)),PV_EVH_StackZero.drop slot (fill w).state,
        (fill w).events ++ PV_EVH_StackZero.emitted slot⟩ := by
  simp only [afterFill,Bind.bind,PV_EVH_StackCleanup.bind,hf,drop64,hs,hn,
    if_true,Pure.pure,PV_EVH_StackCleanup.lift,List.append_nil]

/-- Joins the actual source error branch at opsNative to the partial-fill
cleanup world. It discharges this branch, not the enclosing entry's admission,
success branch, other slots, or the L3 joint observation law. -/
theorem error_native (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_DeployedZeroSelected.selected ops)
    ∀ (key : Key) (fill : Fill) (success : Slice U8 → Q Answer)
      (mask : Array U8 32#usize) (retry : Usize)
      (back : Slice U8 → zeroize.Zeroizing (Array U8 64#usize))
      (w : State) (e : getrandom.error.Error) (s : Slice U8) (slot : Slot),
      (fill w).outcome = .returned (.ok (.Err e,s)) →
      (fill w).state.frame.live.find? (sameKey key) = some slot →
      slot.initialized = 64 →
      PV_EVH_Runtime.sourceProjection (afterFill key fill success w).outcome =
        some (PV_EVH_Entropy.afterDraw mask retry back (.Err e) s) ∧
      Cleared slot (afterFill key fill success w).state ∧
      (afterFill key fill success w).events =
        (fill w).events ++ PV_EVH_StackZero.emitted slot := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_DeployedZeroSelected.selected ops)
  intro key fill success mask retry back w e s slot hf hs hn
  rw [error_world key fill success w e s slot hf hs hn,source_error]
  exact ⟨rfl,PV_EVH_StackZero.dropped_cleared slot (fill w).state,rfl⟩

#print axioms source_error
#print axioms error_world
#print axioms error_native
end PV_EVH_NativeEntropyError
