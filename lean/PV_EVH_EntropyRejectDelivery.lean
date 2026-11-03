import PV_EVH_StackSizedDrop
import PV_EVH_EntropyReturnDelivery
import PV_EVH_EntropyCleanupCounts
set_option autoImplicit false
noncomputable section
namespace PV_EVH_EntropyRejectDelivery
open ProverRwFull
open PV_EVH_StackZero (State Slot)
open PV_EVH_StackCleanup (Q sameKey)
open PV_EVH_EntropyDeployedLayout (original field seed)
open PV_EVH_EntropyMoveKeys (ready)

def checked [ExternalTypes] (owner sp : Nat) (origin : State) : Q Unit := do
  let _ ← PV_EVH_StackSizedDrop.drop 32 (seed owner sp origin).key
  let _ ← PV_EVH_StackSizedDrop.drop 32 (field owner sp origin).key
  PV_EVH_StackSizedDrop.drop 64 (original owner sp origin).key

def completed [ExternalTypes] (owner sp : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) : State :=
  PV_EVH_EntropyRejectCleanup.cleanup (original owner sp w) (field owner sp w)
    (seed owner sp w) (ready owner sp d w)

theorem seed_lookup [ExternalTypes] (owner sp : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) :
    (ready owner sp d w).frame.live.find? (sameKey (seed owner sp w).key) =
      some (seed owner sp w) := by
  change (seed owner sp w :: field owner sp w :: original owner sp w :: w.frame.live).find?
    (sameKey (seed owner sp w).key) = _
  simp only [List.find?_cons,sameKey,beq_self_eq_true,Bool.and_self,if_true]

theorem field_seed_distinct (owner sp : Nat) (w : State) :
    (field owner sp w).key ≠ (seed owner sp w).key :=
  PV_EVH_EntropyInnerFrame.field_seed_distinct owner (sp+64) (sp+96)
    (PV_EVH_EntropyDeployedLayout.entered owner sp w)

theorem field_lookup [ExternalTypes] (owner sp : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) :
    (ready owner sp d w).frame.live.find? (sameKey (field owner sp w).key) =
      some (field owner sp w) := by
  have hs := PV_EVH_EntropyMoveKeys.sameKey_false (field owner sp w) (seed owner sp w)
    (field_seed_distinct owner sp w)
  change (seed owner sp w :: field owner sp w :: original owner sp w :: w.frame.live).find?
    (sameKey (field owner sp w).key) = _
  simp only [List.find?_cons,hs,Bool.false_eq_true,if_false]
  simp only [sameKey,beq_self_eq_true,Bool.and_self,if_true]

/-- All three checked destructors select the original source keys, in source
scope order, without supplied post-cleanup lookups. Retains deployed1.9.0
write/barrier observations. No accepted-path move is used for rejection. -/
theorem checked_run [ExternalTypes] (owner sp : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) :
    checked owner sp w (ready owner sp d w) =
      ⟨.returned (.ok ()),completed owner sp d w,
        PV_EVH_StackZero.emitted (seed owner sp w) ++
        PV_EVH_StackZero.emitted (field owner sp w) ++
        PV_EVH_StackZero.emitted (original owner sp w)⟩ := by
  have ho := PV_EVH_EntropyMoveKeys.original_distinct owner sp w
  have hf := PV_EVH_StackSizedDrop.keeps_lookup (seed owner sp w) (field owner sp w)
    (ready owner sp d w) (field_lookup owner sp d w) (field_seed_distinct owner sp w)
  have horig := PV_EVH_StackSizedDrop.keeps_lookup (field owner sp w) (original owner sp w)
    (PV_EVH_StackZero.drop (seed owner sp w) (ready owner sp d w))
    (PV_EVH_StackSizedDrop.keeps_lookup (seed owner sp w) (original owner sp w)
      (ready owner sp d w) (PV_EVH_EntropyMoveKeys.ready_lookup owner sp d w) ho.2) ho.1
  simp only [checked,Bind.bind,PV_EVH_StackCleanup.bind,
    PV_EVH_StackSizedDrop.returned 32 _ _ _ (seed_lookup owner sp d w) rfl,
    PV_EVH_StackSizedDrop.returned 32 _ _ _ hf rfl,
    PV_EVH_StackSizedDrop.returned 64 _ _ _ horig rfl,
    completed,PV_EVH_EntropyRejectCleanup.cleanup,List.append_assoc]

/-- Repeated source iterations can reuse numeric addresses but not original
lifetime identities. The rejected original owner remains in retired memory. -/
theorem next_original_fresh [ExternalTypes] (owner sp : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) :
    (original owner sp w).key.identity <
      (original owner sp (completed owner sp d w)).key.identity := by
  have hr := PV_EVH_EntropyRejectCleanup.retired (original owner sp w)
    (field owner sp w) (seed owner sp w) (ready owner sp d w)
  have hm : original owner sp w ∈ (completed owner sp d w).frame.live ++
      (completed owner sp d w).frame.retired := by
    apply List.mem_append_right
    change original owner sp w ∈
      (PV_EVH_EntropyRejectCleanup.cleanup _ _ _ _).frame.retired
    rw [hr]
    exact List.mem_cons_self
  exact PV_EVH_EntropySourceSlot.identity_lt _ _ hm

#print axioms seed_lookup
#print axioms field_seed_distinct
#print axioms field_lookup
#print axioms checked_run
#print axioms next_original_fresh
end PV_EVH_EntropyRejectDelivery
