import NLK_LaneProgram
set_option autoImplicit false
set_option pp.proofs false
namespace NMM_Ownership233

/-- One allocation owner retains its complete typed payload. This is a support
carrier; it does not manufacture an admitted native allocation. -/
structure Owned (α : Type) where
  owner : Nat
  payload : α

/-- The four returned boxes from frozen233. No Box is erased to its value. -/
structure Returned (Master Checkpoint Lane Snapshot : Type) where
  master : Owned Master
  checkpoint : Owned Checkpoint
  selectedLane : Owned Lane
  liveSnapshot : Owned Snapshot

def allocationOrder {M C L S : Type} (r : Returned M C L S) : List Nat :=
 [r.master.owner, r.checkpoint.owner, r.selectedLane.owner, r.liveSnapshot.owner]

def cleanupOrder {M C L S : Type} (r : Returned M C L S) : List Nat :=
 [r.liveSnapshot.owner, r.selectedLane.owner, r.checkpoint.owner, r.master.owner]

/-- Distinct live allocations are required from the existing allocator packet;
this theorem cannot be used to assume that an actual parent produced them. -/
def Valid {M C L S : Type} (r : Returned M C L S) : Prop :=
 (allocationOrder r).Nodup

theorem cleanup_reverse {M C L S : Type} (r : Returned M C L S) :
 cleanupOrder r = (allocationOrder r).reverse := by rfl

theorem cleanup_no_double_release {M C L S : Type} (r : Returned M C L S)
 (valid : Valid r) : (cleanupOrder r).Nodup := by
 rw [cleanup_reverse]
 exact List.nodup_reverse.mpr valid

/-- All earlier returned owners are released on a later error/abort. Prefix
length selects the exact lexical acquisition stage, never a successful child. -/
def prefixCleanup {M C L S : Type} (r : Returned M C L S) (acquired : Nat) : List Nat :=
 ((allocationOrder r).take acquired).reverse

theorem cleanup_before_master {M C L S : Type} (r : Returned M C L S) :
 prefixCleanup r 0 = [] := by rfl

theorem cleanup_after_master {M C L S : Type} (r : Returned M C L S) :
 prefixCleanup r 1 = [r.master.owner] := by rfl

theorem cleanup_after_checkpoint {M C L S : Type} (r : Returned M C L S) :
 prefixCleanup r 2 = [r.checkpoint.owner, r.master.owner] := by rfl

theorem cleanup_after_lane {M C L S : Type} (r : Returned M C L S) :
 prefixCleanup r 3 = [r.selectedLane.owner, r.checkpoint.owner, r.master.owner] := by rfl

theorem cleanup_after_snapshot {M C L S : Type} (r : Returned M C L S) :
 prefixCleanup r 4 = cleanupOrder r := by rfl

#print cleanup_reverse
#print axioms cleanup_reverse
#print cleanup_no_double_release
#print axioms cleanup_no_double_release
#print axioms cleanup_before_master
#print axioms cleanup_after_master
#print axioms cleanup_after_checkpoint
#print axioms cleanup_after_lane
#print axioms cleanup_after_snapshot
end NMM_Ownership233
