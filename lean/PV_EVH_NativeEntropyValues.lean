import PV_EVH_EntropyHalves
import PV_EVH_NativeEntropyAccess
import PV_EVH_Entropy
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyValues
open Aeneas Aeneas.Std ProverRwFull ControlFlow
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_EntropyHalves (field seed)
abbrev Answer [ExternalTypes] := ControlFlow Usize (core.result.Result
  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
  aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError)

/-- Exact remaining source tests, including their short-circuit order. The
nonzero scan is the extracted function, not a supplied whole-helper answer. -/
def tests [ExternalTypes] [ExternalFuns] (mask : Array U8 32#usize)
    (retry : Usize) (a : Array U8 64#usize) : Result Answer := do
  let b ← aspis_prover.state_only_entropy.entropy_nonzero32 (field a)
  if b then
    let c ← aspis_prover.state_only_entropy.entropy_nonzero32 (seed a)
    if c then
      pure (done (.Ok ⟨mask,field a,seed a⟩))
    else pure (cont (Usize.wrapping_add retry 1#usize))
  else pure (cont (Usize.wrapping_add retry 1#usize))

/-- Restores the original fill borrow and BOTH copy continuations at the
actual installed native dictionary. No hypothesis supplies slice/index/copy
answers. This value law does not erase their native memory observations. -/
theorem after_draw (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ (mask : Array U8 32#usize) (retry : Usize) (before a : Array U8 64#usize),
      PV_EVH_Entropy.afterDraw mask retry (Array.to_slice_mut before).2
        (.Ok ()) (Array.to_slice a) = tests mask retry a := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro mask retry before a
  unfold PV_EVH_Entropy.afterDraw
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  have hrestore : (Array.to_slice_mut before).2 (Array.to_slice a) = a :=
    PV_EVH_NativeEntropyBorrow.restore_array _ before a
  rw [hrestore]
  simp only [PV_EVH_NativeZeroWrappers.constructor_native base heap box ops,
    PV_EVH_NativeEntropyAccess.deref_mut_native base heap box ops,
    PV_EVH_NativeEntropyAccess.deref_native base heap box ops,
    bind_tc_ok,Aeneas.Std.lift,PV_EVH_EntropyHalves.first_index,
    PV_EVH_EntropyHalves.second_index,PV_EVH_EntropyHalves.copy32,
    PV_EVH_EntropyHalves.restored,id_eq]
  rfl

#print axioms after_draw
end PV_EVH_NativeEntropyValues
