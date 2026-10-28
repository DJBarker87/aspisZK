import R1Z.PV_RDB2D_MasksValue
namespace R1Z.PV_RDB2D_MasksWorld
open Aeneas Aeneas.Std Result PV_RDB2D_CollectorTrace PV_RDB2D_CollectorProgram
set_option autoImplicit false

/-- Loop consumes the current entire array at every step. Vec iteration itself
is nonallocating; its final destructor sees the original capacity272, even
though only214 rows remain after dedup. -/
def loopAndDrop {S F : Type} (deallocate : Nat → Nat → Nat → S → Result S)
    (r : Returned × State S F) : Result (Except PV_B3P_Schedule133.Error PV_RDB2D_MasksLoop.Masks × State S F) := do
  match r.1 with
  | .error e => ok (.error e,r.2)
  | .ok rows =>
    let masks := PV_RDB2D_MasksLoop.run rows.values PV_RDB2D_MasksValue.initial
    let state ← release deallocate rows.address 544 r.2
    ok (.ok masks,state)

def source {S F : Type} (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler S F) (state : State S F) :=
  PV_RDB2D_CollectorProgram.source allocate deallocate handler state >>= loopAndDrop deallocate

def reference {S F : Type} (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler S F) (state : State S F) :=
  PV_RDB2D_CollectorProgram.reference allocate deallocate handler state >>= loopAndDrop deallocate

theorem complete {S F : Type} (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler S F) (state : State S F) :
    source allocate deallocate handler state=reference allocate deallocate handler state := by
  unfold source reference
  rw [PV_RDB2D_CollectorProgram.complete]

theorem returned_rows {S F : Type} (deallocate : Nat → Nat → Nat → S → Result S)
    (address : Nat) (state : State S F) :
    loopAndDrop deallocate (.ok (sortedBuffer address),state) =
      (do let after ← release deallocate address 544 state
          ok (.ok PV_RDB2D_MasksValue.value,after)) := by
  simp only [loopAndDrop,sortedBuffer,PV_RDB2D_MasksValue.concrete]

theorem drop_public_layout (address left right : Nat) :
    (fun (_ : Nat) => (.deallocate 544 2 : Action)) left=
      (fun (_ : Nat) => (.deallocate 544 2 : Action)) right := rfl

#print axioms complete
#print axioms returned_rows
#print axioms drop_public_layout
end R1Z.PV_RDB2D_MasksWorld
