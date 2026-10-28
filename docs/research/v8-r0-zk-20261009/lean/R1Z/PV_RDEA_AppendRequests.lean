import R1Z.PV_RDEA_CapacityEndpoint
import R1Z.PV_RDB1_Append
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_AppendRequests
open PV_RDB1_V183_ReserveWorld PV_RDB1_Append PV_RDEA_CapacityEndpoint

/-- The request word is a function of public header lengths and append count;
no input byte, allocator address or private state is inspected. -/
def requests (wordMax byteMax len cap count : Nat) : List (Nat × Nat × Nat) :=
  if count ≤ cap-len then [] else
  if len+count>wordMax then [] else
  if growthCapacity len cap count>byteMax then [] else
  [(cap,growthCapacity len cap count,1)]

theorem finishAt_sizes {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (b : Buffer U8)
    (count : Nat) (w : World S F) :
    sizes (finishAt step shape b count w).world.history = sizes w.history ++
      [(b.capacity,growthCapacity b.values.length b.capacity count,1)] := by
  unfold finishAt
  dsimp only
  cases h : step ⟨b.address,b.capacity,growthCapacity b.values.length b.capacity count,shape⟩ w.allocator with
  | mk p s => cases p <;> simp [h,attempted,succeeded,sizes,width]

theorem reserve_requests {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (width : shape.width=1)
    (b : Buffer U8) (count : Nat) (w : World S F) :
    sizes (reserve step wordMax byteMax shape b count w).world.history =
      sizes w.history ++ requests wordMax byteMax b.values.length b.capacity count := by
  unfold reserve requests
  simp only [width,Nat.mul_one]
  split <;> try simp [sizes]
  split <;> try simp [sizes]
  split <;> try simp [sizes]
  exact finishAt_sizes step shape width b count w

/-- Actual byte-append includes the reserve request even on error and performs
no additional allocator request during the copy/length update. -/
theorem append_requests {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (width : shape.width=1)
    (b : Buffer U8) (tail : List U8) (w : World S F) :
    sizes (source step wordMax byteMax shape b tail w).world.history =
      sizes w.history ++ requests wordMax byteMax b.values.length b.capacity tail.length := by
  unfold source appendAfter
  split <;> exact reserve_requests step wordMax byteMax shape width b tail.length w

/-- Same public header/count gives the same request schedule even when live
bytes, allocation addresses, private states and allocator outcomes differ. -/
theorem public_request_word (wordMax byteMax len cap count len' cap' count' : Nat)
    (hlen : len=len') (hcap : cap=cap') (hcount : count=count') :
    requests wordMax byteMax len cap count=requests wordMax byteMax len' cap' count' := by
  rw [hlen,hcap,hcount]

/-- Capacity on the successful branch, as selected by the public reserve guard. -/
def nextCapacity (len cap count : Nat) : Nat :=
  if count≤cap-len then cap else growthCapacity len cap count

theorem reserve_success_capacity {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer U8)
    (count : Nat) (w : World S F)
    (success : (reserve step wordMax byteMax shape b count w).returned=.ok ()) :
    (reserve step wordMax byteMax shape b count w).buffer.capacity=
      nextCapacity b.values.length b.capacity count := by
  unfold reserve at success ⊢
  unfold nextCapacity
  split <;> try rfl
  split
  · cases success
  · split
    · cases success
    · unfold finishAt at success ⊢
      dsimp only at success ⊢
      cases h : step ⟨b.address,b.capacity,growthCapacity b.values.length b.capacity count,shape⟩ w.allocator with
      | mk p s => cases p <;> simp [h] at success ⊢

#print axioms finishAt_sizes
#print axioms reserve_requests
#print axioms append_requests
#print axioms public_request_word
#print axioms reserve_success_capacity
end R1Z.PV_RDEA_AppendRequests
