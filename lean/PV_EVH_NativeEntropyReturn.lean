import PV_EVH_EntropyDecision
import PV_EVH_EntropyCleanupCounts
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyReturn
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_StackZero (Slot State Cleared)
open PV_EVH_StackCleanup (Q sameKey drop64)
open PV_EVH_EntropyDecision (Accepted)
open PV_EVH_HeapOwnership (Key)
variable [ExternalTypes]

/-- Return-place moves occur BEFORE original64's scope destructor. The actual
move primitive is OPEN and receives both source slots and the exact restored
source values. It must account for returned ownership and moved-from residues;
no cleanup of either moved-from32 slot is invented. -/
def finish (original : Key) (field seed : Slot)
    (mask : Array U8 32#usize) (a : Array U8 64#usize)
    (move : Slot → Slot → aspis_prover.state_only_entropy.StateOnlyAttemptSecrets → Q Unit) :
    Q PV_EVH_NativeEntropyValues.Answer := do
  let _ ← move field seed ⟨mask,PV_EVH_EntropyHalves.field a,PV_EVH_EntropyHalves.seed a⟩
  let _ ← drop64 original
  pure (Accepted mask a)

theorem returned_world (original field seed : Slot)
    (mask : Array U8 32#usize) (a : Array U8 64#usize)
    (move : Slot → Slot → aspis_prover.state_only_entropy.StateOnlyAttemptSecrets → Q Unit)
    (w : State)
    (hm : (move field seed ⟨mask,PV_EVH_EntropyHalves.field a,PV_EVH_EntropyHalves.seed a⟩ w).outcome =
      .returned (.ok ()))
    (hl : (move field seed ⟨mask,PV_EVH_EntropyHalves.field a,PV_EVH_EntropyHalves.seed a⟩ w).state.frame.live.find?
      (sameKey original.key) = some original)
    (hn : original.initialized = 64) :
    let m := move field seed ⟨mask,PV_EVH_EntropyHalves.field a,PV_EVH_EntropyHalves.seed a⟩ w
    finish original.key field seed mask a move w =
      ⟨.returned (.ok (Accepted mask a)),PV_EVH_StackZero.drop original m.state,
        m.events ++ PV_EVH_StackZero.emitted original⟩ := by
  simp only [finish,Bind.bind,PV_EVH_StackCleanup.bind,hm,drop64,hl,hn,
    if_true,Pure.pure,PV_EVH_StackCleanup.lift,List.append_nil]

/-- Native move abort/fault prefixes survive and original cleanup is not
fabricated on that terminal branch. No move implementation is assumed. -/
theorem move_fault (original : Key) (field seed : Slot)
    (mask : Array U8 32#usize) (a : Array U8 64#usize)
    (move : Slot → Slot → aspis_prover.state_only_entropy.StateOnlyAttemptSecrets → Q Unit)
    (w : State) (e : PV_EVH_Runtime.Fault)
    (hm : (move field seed ⟨mask,PV_EVH_EntropyHalves.field a,PV_EVH_EntropyHalves.seed a⟩ w).outcome =
      .fault e) :
    finish original field seed mask a move w =
      let m := move field seed ⟨mask,PV_EVH_EntropyHalves.field a,PV_EVH_EntropyHalves.seed a⟩ w
      ⟨.fault e,m.state,m.events⟩ := by
  simp only [finish,Bind.bind,PV_EVH_StackCleanup.bind,hm]

#print axioms returned_world
#print axioms move_fault
end PV_EVH_NativeEntropyReturn
