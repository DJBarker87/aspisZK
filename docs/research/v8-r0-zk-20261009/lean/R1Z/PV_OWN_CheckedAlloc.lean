import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_CheckedAlloc
open PV_OWN_Heap PV_OWN_Operations PV_W_Threading
structure Command {S X E : Type} (primitive : Request → S → Outcome E (Option Nat) × S)
 (w : State S X) where
 request : Request
 owner : Nat
 empty : w.memory.slots owner=none
 nonzero : request.size>0
 valid : Valid w.memory.heap
 old_nonzero : ∀ q c, w.memory.heap q=some c → c.live=true → c.size>0
 runtime_adequacy : AllocatorAdequate primitive request w

theorem fresh {S X E : Type} (primitive : Request → S → Outcome E (Option Nat) × S)
 (w : State S X) (cmd : Command primitive w) (p : Nat) (s : S)
 (h:primitive cmd.request w.allocator=(.ok (some p),s)) :
 ∀ c, w.memory.heap p=some c → c.live=true → False := by
 intro c hc hl
 have hd:=(cmd.runtime_adequacy p s h).2.2.2 p c hc hl
 have hp:=cmd.old_nonzero p c hc hl
 have hn:=cmd.nonzero
 omega

theorem owned_success {S X E : Type} (primitive : Request → S → Outcome E (Option Nat) × S)
 (w : State S X) (cmd : Command primitive w) (p : Nat) (s : S)
 (h:primitive cmd.request w.allocator=(.ok (some p),s)) :
 Owned (allocate primitive cmd.request cmd.owner w).world.memory cmd.owner
  ⟨p,w.memory.generations p+1⟩ (emptyCell cmd.request.size cmd.request.alignment cmd.owner) := by
 simp [Owned,Live,allocate,emit,h,put,emptyCell]
#print axioms fresh
#print axioms owned_success
end R1Z.PV_OWN_CheckedAlloc
