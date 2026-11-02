import PV_EVH_EntropyReturnLayout
set_option autoImplicit false
namespace PV_EVH_EntropyMoveKeys
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackCleanup (sameKey)
open PV_EVH_EntropyDeployedLayout (original field seed entered)
open PV_EVH_EntropyReturnLayout (returnedField returnedSeed)

/-- Source initializer order derives actual ghost lifetime distinctions.
This is independent of the recorded numeric separation, not its replacement. -/
theorem original_distinct (owner sp : Nat) (w : State) :
    (original owner sp w).key ≠ (field owner sp w).key ∧
    (original owner sp w).key ≠ (seed owner sp w).key := by
  have ho : original owner sp w ∈ (entered owner sp w).frame.live := by
    change original owner sp w ∈ original owner sp w :: w.frame.live
    exact List.mem_cons_self
  exact PV_EVH_EntropyInnerFrame.old_distinct owner (sp+64) (sp+96)
    (entered owner sp w) (original owner sp w) ho

theorem sameKey_false (old dst : Slot) (hne : old.key ≠ dst.key) :
    sameKey old.key dst = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have ht : dst.key.identity = old.key.identity ∧ dst.key.owner = old.key.owner := by
    simpa only [sameKey,Bool.and_eq_true,beq_iff_eq] using h
  have he : old.key = dst.key := by
    cases ho : old.key
    cases hd : dst.key
    simp_all
  exact hne he

/-- Derives the post-move original lookup for the EXISTING relocation pair.
Only the pre-move original lookup remains; no supplied post-move answer/key
inequality is needed. Complete actual Self/staging/observations remain P. -/
theorem original_lookup (owner sp result : Nat) (w origin : State)
    (hl : w.frame.live.find? (sameKey (original owner sp origin).key) =
      some (original owner sp origin)) :
    (PV_EVH_EntropyMoveBacking.pair (field owner sp origin) (seed owner sp origin)
      (returnedField owner sp result origin) (returnedSeed owner sp result origin) w).frame.live.find?
        (sameKey (original owner sp origin).key) = some (original owner sp origin) := by
  have h := original_distinct owner sp origin
  exact PV_EVH_EntropyMoveBacking.original_lookup _ _ _ _ _ w hl h.1 h.2
    (sameKey_false _ _ h.1) (sameKey_false _ _ h.2)

/-- The actual initializer/fill/copy ordering, including original64 admission.
This defines only the already checked physical-state interpretation. -/
noncomputable def ready [ProverRwFull.ExternalTypes] (owner sp : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) : State :=
  PV_EVH_EntropyPhysicalCopy.copies (original owner sp w) (field owner sp w) (seed owner sp w)
    (PV_EVH_EntropyPhysicalCopy.admit_pair (field owner sp w) (seed owner sp w)
      (PV_EVH_StackEntropyFill.post (original owner sp w) d (entered owner sp w)))

/-- The remaining pre-move original lookup follows from the source-shaped
state, not from a supplied lookup answer. -/
theorem ready_lookup [ProverRwFull.ExternalTypes] (owner sp : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) :
    (ready owner sp d w).frame.live.find? (sameKey (original owner sp w).key) =
      some (original owner sp w) := by
  have h := original_distinct owner sp w
  have hf := sameKey_false (original owner sp w) (field owner sp w) h.1
  have hs := sameKey_false (original owner sp w) (seed owner sp w) h.2
  change (seed owner sp w :: field owner sp w :: original owner sp w :: w.frame.live).find?
    (sameKey (original owner sp w).key) = some (original owner sp w)
  simp only [List.find?_cons,hs,hf,Bool.false_eq_true,if_false]
  simp only [sameKey,beq_self_eq_true,Bool.and_self,if_true]

theorem moved_ready_lookup [ProverRwFull.ExternalTypes] (owner sp result : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State) :
    (PV_EVH_EntropyMoveBacking.pair (field owner sp w) (seed owner sp w)
      (returnedField owner sp result w) (returnedSeed owner sp result w)
      (ready owner sp d w)).frame.live.find? (sameKey (original owner sp w).key) =
        some (original owner sp w) :=
  original_lookup owner sp result (ready owner sp d w) w (ready_lookup owner sp d w)

#print axioms original_distinct
#print axioms sameKey_false
#print axioms original_lookup
#print axioms ready_lookup
#print axioms moved_ready_lookup
end PV_EVH_EntropyMoveKeys
