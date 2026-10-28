import R1Z.PV_RDEA_V181
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_CapacityEndpoint
open PV_RDB1_V183_ReserveWorld

/-- Size/order observation only. Addresses and allocator outcomes are retained
in the full world, and are NOT erased from the endpoint observation. -/
def sizes (events : List Event) : List (Nat × Nat × Nat) :=
  events.map (fun e => (e.request.oldCapacity,e.request.newCapacity,e.request.shape.width))

theorem finish_sizes {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address n : Nat) (w : World S F) :
    sizes (finish step shape (PV_RDB1_V181.empty address) n w).world.history =
      sizes w.history ++ [(0,n,shape.width)] := by
  have h := PV_RDB1_V183_ReserveFacts.finish_effects step shape
    (PV_RDB1_V181.empty address) n w
  rw [h.2.2.2.2.2.2]
  simp [sizes,PV_RDB1_V181.empty]

/-- At the source literal call there is exactly one request of 69 bytes,
including when the allocator fails and whatever private state preceded it. -/
theorem literal_sizes {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat) (w : World S F) :
    sizes (PV_RDB1_V181.deployed step 18446744073709551615
      9223372036854775807 shape address 69 w).world.history =
      sizes w.history ++ [(0,69,1)] := by
  rw [show 69=PV_RDEA_V181.reservationCapacity from rfl,
    PV_RDEA_V181.reachable_constructor step shape width]
  simpa only [PV_RDEA_V181.reservationCapacity,width] using
    finish_sizes step shape address 69 w

/-- Explicit allocation-failure branch; the state returned by the allocator
is preserved, with its failed request recorded. No success premise. -/
theorem literal_failure {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat) (w : World S F)
    (s : S) (failed : step ⟨address,0,69,shape⟩ w.allocator=(none,s)) :
    let e := PV_RDB1_V181.deployed step 18446744073709551615
      9223372036854775807 shape address 69 w
    e.returned=.error (.allocError ⟨usize 69,shape.align⟩) ∧
      e.buffer.values=[] ∧ e.world.allocator=s ∧
      e.world.history=w.history++[⟨⟨address,0,69,shape⟩,none⟩] := by
  dsimp only
  rw [show 69=PV_RDEA_V181.reservationCapacity from rfl,
    PV_RDEA_V181.reachable_constructor step shape width]
  simp [finish,PV_RDB1_V181.empty,PV_RDEA_V181.reservationCapacity,
    failed,width,attempted]

/-- The constructor continuation receives its actual buffer and world only on
success. The failure handler receives the exact error and post-request world. -/
def consume {S F R : Type} (e : Execution U8 S F)
    (failure : PV_RDB1_V183_ReserveWorld.Error → World S F → R)
    (success : Buffer U8 → World S F → R) : R :=
  match e.returned with
  | .error err => failure err e.world
  | .ok () => success e.buffer e.world

theorem failure_consumed {S F R : Type} (e : Execution U8 S F)
    (failure : PV_RDB1_V183_ReserveWorld.Error → World S F → R) (success : Buffer U8 → World S F → R)
    (err : PV_RDB1_V183_ReserveWorld.Error) (h : e.returned=.error err) :
    consume e failure success=failure err e.world := by
  simp only [consume,h]

theorem endpoint_repaired {S F R : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address n : Nat) (w : World S F)
    (failure : PV_RDB1_V183_ReserveWorld.Error → World S F → R)
    (success : Buffer U8 → World S F → R) :
    consume (PV_RDB1_V181.deployed step 18446744073709551615
      9223372036854775807 shape address n w) failure success =
    consume (PV_RDB1_V181.reference step 18446744073709551615
      9223372036854775807 shape address n w) failure success := by
  rw [PV_RDB1_V181.complete step _ _ shape width]

/-- Caller supplies public n; the successful/request branch is selected by
public arithmetic only, independent of allocator state or payload values. -/
def requestSizes (n : Nat) : List (Nat × Nat × Nat) :=
  if n>18446744073709551615 then [] else
  if n>9223372036854775807 then [] else
  if n=0 then [] else [(0,n,1)]

theorem all_sizes {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address n : Nat) (w : World S F) :
    sizes (PV_RDB1_V181.deployed step 18446744073709551615
      9223372036854775807 shape address n w).world.history =
      sizes w.history ++ requestSizes n := by
  unfold PV_RDB1_V181.deployed requestSizes
  simp only [width,Nat.mul_one]
  split <;> try simp [sizes]
  split <;> try simp [sizes]
  split <;> try simp [sizes]
  simpa only [width,sizes] using finish_sizes step shape address n w

#print axioms finish_sizes
#print axioms literal_sizes
#print axioms literal_failure
#print axioms failure_consumed
#print axioms endpoint_repaired
#print axioms all_sizes
end R1Z.PV_RDEA_CapacityEndpoint
