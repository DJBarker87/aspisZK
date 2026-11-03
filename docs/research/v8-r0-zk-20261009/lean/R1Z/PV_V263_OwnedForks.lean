import R1Z.PV_V263_GrowingPush
import R1Z.PV_V263_RetainedSpine
/-! Handle-Vec source loop using exact growth decisions instead of arbitrary
push-method effects. Delayed task bodies remain the retained source families.
This local loop is not yet installed in a complete native worker interpreter. -/
set_option autoImplicit false
namespace R1Z.PV_V263_OwnedForks
open Aeneas Aeneas.Std PV_V263_World PV_V263_OwnedDrain
abbrev Layout := PV_V263_PublicRequests.Layout

def empty {A : Type} (layout : Layout) : Owner A :=
  ⟨PV_V263_VectorDrain.empty 0 (Nat.zero_le _),
   ⟨layout.align,0,layout,Nat.zero_le _⟩,Nat.zero_le _⟩

def forks {S A : Type} (runtime : PV_V263_RetainedMethods.Runtime S)
    (growth : PV_V263_RawGrowth.Runtime S) (layouts : PV_V263_RetainedMethods.Layouts)
    (n : Usize) (callback : Nat → Q S A) :
    List Nat → Owner (PV_V263_RetainedSpine.Task S A) →
      Q S (Owner (PV_V263_RetainedSpine.Task S A))
  | [],handles => lift (.ok handles)
  | k::ks,handles =>
      PV_V263_World.bind
        (PV_V263_DeferredJoin.fork runtime.methods.os k
          (PV_V263_RetainedSpine.caughtFamily runtime layouts n k callback)) fun task =>
      PV_V263_World.bind (PV_V263_GrowingPush.push growth handles task) fun handles' =>
      forks runtime growth layouts n callback ks handles'

theorem empty_raw (layout : Layout) :
    (empty (A := Unit) layout).allocation.rawCapacity=0 ∧
    (empty (A := Unit) layout).allocation.pointer=layout.align ∧
    release (empty (A := Unit) layout).allocation=none := by
  simp only [empty,release,or_true,if_true,and_self]

/-- A spawn fault occurs before a handle push, callback, or remaining spawn.
The exact OS post-world and event prefix survive. -/
theorem spawn_fault {S A : Type} (runtime : PV_V263_RetainedMethods.Runtime S)
    (growth : PV_V263_RawGrowth.Runtime S) (layouts : PV_V263_RetainedMethods.Layouts)
    (n : Usize) (callback : Nat → Q S A) (k : Nat) (ks : List Nat)
    (handles : Owner (PV_V263_RetainedSpine.Task S A)) (w : State S) (error : Fault)
    (h : (PV_V263_WorkerRequests.spawn runtime.methods.os k w).outcome=.fault error) :
    forks runtime growth layouts n callback (k::ks) handles w=⟨.fault error,
      (PV_V263_WorkerRequests.spawn runtime.methods.os k w).state,
      (PV_V263_WorkerRequests.spawn runtime.methods.os k w).events⟩ := by
  simp only [forks,PV_V263_DeferredJoin.fork,PV_V263_World.bind,h]

#print axioms empty
#print axioms forks
#print axioms empty_raw
#print axioms spawn_fault
end R1Z.PV_V263_OwnedForks
