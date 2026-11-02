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

#print axioms original_distinct
#print axioms sameKey_false
#print axioms original_lookup
end PV_EVH_EntropyMoveKeys
