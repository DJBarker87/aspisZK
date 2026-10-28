import R1Z.PV_RDEA_V178ConsumedLaw
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEAC_OwnedCleanup
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath

/-- The u8-owned argument's RawVec destructor. Its allocator primitive retains
private state; neither old bytes nor the surrounding frame are discarded. -/
def release {S F : Type} (free : Nat → Nat → Nat → S → S)
    (owned : Buffer U8) (w : World S F) : World S F :=
  if owned.capacity=0 then w else
  {w with allocator:=free owned.address owned.capacity 1 w.allocator
          deallocCalls:=w.deallocCalls+1
          live:=fun a => if a=owned.address then false else w.live a}

theorem effects {S F : Type} (free : Nat → Nat → Nat → S → S)
    (owned : Buffer U8) (w : World S F) :
    (release free owned w).frame=w.frame ∧
    (release free owned w).memory=w.memory ∧
    (release free owned w).history=w.history := by
  unfold release
  split <;> exact ⟨rfl,rfl,rfl⟩

theorem allocated {S F : Type} (free : Nat → Nat → Nat → S → S)
    (owned : Buffer U8) (w : World S F) (h : owned.capacity≠0) :
    (release free owned w).allocator=free owned.address owned.capacity 1 w.allocator ∧
    (release free owned w).deallocCalls=w.deallocCalls+1 ∧
    (release free owned w).live owned.address=false := by
  simp only [release,h,if_false,if_true,and_self]

/-- Success of Path::join<P=String> destroys P before the caller proceeds.
The consumed library-body law remains inside this call-site cleanup. -/
def returningConsumer {S F R : Type} (free : Nat → Nat → Nat → S → S)
    (owned : Buffer U8) (e : Outcome (Buffer U8) S F)
    (failure : PV_RDB1_V183_ReserveWorld.Error → World S F → R)
    (next : List U8 → World S F → R) : R :=
  PV_RDEA_JoinConsumer.consume e failure (fun bytes w => next bytes (release free owned w))

theorem consumed {S F R : Type} (step : Request → S → Option Nat × S)
    (free : Nat → Nat → Nat → S → S) (owned : Buffer U8)
    (shape : Shape) (width : shape.width=1) (address : Nat) (absolute needSep : Bool)
    (base path : List U8) (w : World S F)
    (failure : PV_RDB1_V183_ReserveWorld.Error → World S F → R)
    (next : List U8 → World S F → R) :
    let e := sourceJoin (PV_RDEA_CloneExecution.clone step shape address)
      (PV_RDEA_AppendExecution.append step shape) absolute needSep base path w
    returningConsumer free owned e failure next=
      (match e.1 with
       | .error err => failure err e.2
       | .ok _ => next (PV_RDEA_PushValues.value base path absolute needSep) (release free owned e.2)) ∧
    PV_RDEA_PrefixWords.Prefix (PV_RDEA_CapacityEndpoint.sizes e.2.history)
      (PV_RDEA_CapacityEndpoint.sizes w.history++PV_RDEA_PathSchedule.joinWord base.length path.length absolute needSep) := by
  exact PV_RDEA_V178ConsumedLaw.consumed step shape width address absolute needSep base path w
    failure (fun bytes w => next bytes (release free owned w))

/-- Erasing this cleanup is incompatible with exact post-world equality.
This is a proof-boundary obstruction, not a witness-dependence claim. -/
theorem cannot_erase {S F : Type} (free : Nat → Nat → Nat → S → S)
    (owned : Buffer U8) (w : World S F) (h : owned.capacity≠0) :
    release free owned w≠w := by
  intro eq
  have hc := congrArg (fun w : World S F => w.deallocCalls) eq
  have effect := (allocated free owned w h).2.1
  omega

#print axioms effects
#print axioms allocated
#print axioms consumed
#print axioms cannot_erase
end R1Z.PV_RDEAC_OwnedCleanup
